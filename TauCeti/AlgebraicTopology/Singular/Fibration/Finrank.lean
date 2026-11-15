/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.AlgebraicTopology.Singular.Empty
import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Finrank
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Finiteness, vanishing and Euler's equality for the homology of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration and `(C, D)` a relative CW complex in a Hausdorff space `B`
with skeleta `Xⁿ = skeletonLT C (n + 1)`. Filtering `p⁻¹(C)` above `p⁻¹(D)` by the preimages
`Eₙ = p⁻¹(Xⁿ)` of the skeleta expresses the relative homology `Hᵢ(p⁻¹(C), p⁻¹(D); R)` in terms of
the homology of the fibres `p⁻¹(χⱼ(0))` over the centres of the cells of `C`:

* in degrees `i < k`, the step `Hᵢ(Eₖ, Eₖ₋₁; R)` vanishes
  (`TauCeti.TopCat.isZero_singularHomology_preimageSkeletonPair_of_lt`), while in degree `q + k` it
  is `⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)` over the `k`-cells `j` of `C`
  (`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`);
* the inclusion `(p⁻¹(Xⁿ), p⁻¹(D)) ⟶ (p⁻¹(C), p⁻¹(D))` induces an epimorphism on `Hₙ` and an
  isomorphism on `Hₘ` for `m < n`, with no dimension bound on `C`
  (`TauCeti.TopCat.epi_singularHomologyMap_preimage_skeletonLT`,
  `TauCeti.TopCat.isIso_singularHomologyMap_preimage_skeletonLT`);
* **finiteness**: over a Noetherian ring `R`, if `C` has finitely many cells in dimensions `≤ i`
  and the fibres over their centres have finitely generated `H_{i - m}`, then
  `Hᵢ(p⁻¹(C), p⁻¹(D); R)` is finitely generated, with no dimension bound on `C` or on the fibres
  (`TauCeti.TopCat.finite_singularHomology_preimage_base_subset_complex`);
* **subadditivity**: over a division ring `R`, under the same hypothesis,
  `dim Hᵢ(p⁻¹(C), p⁻¹(D); R) ≤ ∑_{m ≤ i} ∑ⱼ dim H_{i - m}(p⁻¹(χⱼ(0)); R)`
  (`TauCeti.TopCat.finrank_singularHomology_preimage_base_subset_complex_le`);
* **vanishing**: over any ring `R`, if `C` has no cells in dimensions `≥ d` and the fibres over
  cell centres have vanishing homology above degree `Q`, then `Hᵢ(p⁻¹(C), p⁻¹(D); R) = 0` for
  `d + Q ≤ i` (`TauCeti.TopCat.isZero_singularHomology_preimage_base_subset_complex_of_le`); for a
  finite relative CW complex, pointwise eventual vanishing on cell-centre fibres implies eventual
  vanishing on `(p⁻¹(C), p⁻¹(D))`
  (`TauCeti.TopCat.eventually_isZero_singularHomology_preimage_base_subset_complex`);
* **Euler's equality**: over a division ring `R`, when `(C, D)` is a finite relative CW complex
  and each cell-centre fibre has finite-dimensional, eventually vanishing homology, the alternating
  sum of dimensions of `Hᵢ(p⁻¹(C), p⁻¹(D); R)` equals the cellwise alternating sum of the fibre
  Euler characteristics
  (`TauCeti.TopCat.finsum_finrank_singularHomology_preimage_base_subset_complex`), and equals
  `cwEulerChar C · c` when every cell-centre fibre has alternating homology dimension sum `c`
  (`TauCeti.TopCat.finsum_finrank_singularHomology_preimage_base_subset_complex_of_eq`).

For an absolute CW complex `C` the empty-subspace comparison reads these statements on `p⁻¹(C)`,
and for `C = univ` on `E` itself. Base-changing `p` along a weak homotopy equivalence `g : B' ⟶ B`
from a space `B'` carrying a CW structure on `univ` extends them to Serre fibrations over bases `B`
with neither a Hausdorff hypothesis nor a CW structure of their own.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44, and Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section SkeletonPair

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u)

include hp

/-- **Consecutive skeletal preimages of a Serre fibration have no homology below the cell
dimension**: `Hᵢ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R) = 0` for `i < k`. -/
theorem isZero_singularHomology_preimageSkeletonPair_of_lt [Ring R] {k i : ℕ} (hi : i < k) :
    IsZero ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i) := by
  rw [← ofInclusion_preimageSkeleton_eq_preimageSkeletonPair k (k - 1 : ℤ) rfl]
  exact isZero_singularHomology_preimageSkeleton_succ hp R (k - 1) i (by lia)

/-- `Hᵢ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R)` vanishes whenever either `i < k` or every `k`-cell centre fibre
has vanishing `H_{i - k}`. -/
theorem isZero_singularHomology_preimageSkeletonPair_of_forall_cell [Ring R] {k i : ℕ}
    (h : k ≤ i → ∀ j : cell C k, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - k)).obj
        (ModuleCat.of R R)).obj (p.fiber (map k j 0)))) :
    IsZero ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i) := by
  rcases lt_or_ge i k with hik | hki
  · exact isZero_singularHomology_preimageSkeletonPair_of_lt hp R hik
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + k := ⟨i - k, (Nat.sub_add_cancel hki).symm⟩
    refine (preimageSkeletonPairSingularHomologyIsoSigma C hp R k q).isZero_iff.2 ?_
    rw [IsZero.iff_id_eq_zero]
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    have hj := h hki j
    rw [Nat.add_sub_cancel] at hj
    exact hj.eq_of_src _ _

/-- If there are finitely many `k`-cells and for `k ≤ i` every `k`-cell centre fibre has finitely
generated `H_{i - k}`, then `Hᵢ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R)` is finitely generated. -/
theorem finite_singularHomology_preimageSkeletonPair [Ring R] (k i : ℕ) [_root_.Finite (cell C k)]
    (h : k ≤ i → ∀ j : cell C k, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - k)).obj
        (ModuleCat.of R R)).obj (p.fiber (map k j 0)))) :
    Module.Finite R ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i :
      ModuleCat R) := by
  classical
  rcases lt_or_ge i k with hik | hki
  · have : Subsingleton ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i :
        ModuleCat R) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_singularHomology_preimageSkeletonPair_of_lt (C := C) hp R hik)
    infer_instance
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + k := ⟨i - k, (Nat.sub_add_cancel hki).symm⟩
    have (j : cell C k) : Module.Finite R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map k j 0))) := by
      have hj := h hki j
      rwa [Nat.add_sub_cancel] at hj
    exact Module.Finite.equiv
      (preimageSkeletonPairSingularHomologyIsoSigma C hp R k q ≪≫
        ModuleCat.coprodIsoDirectSum _).symm.toLinearEquiv

/-- Over a division ring `R`, if there are finitely many `k`-cells and every `k`-cell centre fibre
has finite-dimensional `Hq`, then `dim H_{q + k}(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R)` is the sum over the
`k`-cells `j` of `dim Hq(p⁻¹(χⱼ(0)); R)`. -/
theorem finrank_singularHomology_preimageSkeletonPair_add [DivisionRing R] (k q : ℕ)
    [_root_.Finite (cell C k)]
    (h : ∀ j : cell C k, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map k j 0)))) :
    finrank R ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) (q + k) :
        ModuleCat R) =
      ∑ᶠ j : cell C k, finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map k j 0))) := by
  classical
  cases nonempty_fintype (cell C k)
  rw [(preimageSkeletonPairSingularHomologyIsoSigma C hp R k q ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv.finrank_eq, Module.finrank_directSum,
    finsum_eq_sum_of_fintype]

/-- Over a division ring `R`, the truncated alternating sum of dimensions of
`Hᵢ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R)` through degree `N ≥ k + Q`, when every `k`-cell centre fibre has
finite-dimensional homology through degree `Q` and vanishing homology above `Q`, is `(-1)ᵏ` times
the sum of the fibre Euler characteristics over the `k`-cells. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_preimageSkeletonPair [DivisionRing R]
    {k Q N : ℕ} [_root_.Finite (cell C k)] (hQN : k + Q ≤ N)
    (hfin : ∀ (j : cell C k) (q : ℕ), q ≤ Q → Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map k j 0))))
    (hzero : ∀ (j : cell C k) (q : ℕ), Q < q → IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map k j 0)))) :
    ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
        finrank R ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i :
          ModuleCat R) =
      (-1 : ℤ) ^ k * ∑ᶠ j : cell C k, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map k j 0))) := by
  cases nonempty_fintype (cell C k)
  -- Split off degrees `< k` (where the step vanishes) and degrees `> k + Q` (where fibres vanish).
  have hsplit : N + 1 = k + ((Q + 1) + (N - (k + Q))) := by lia
  have hlow : ∑ i ∈ Finset.range k, (-1 : ℤ) ^ i *
      finrank R ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) i :
        ModuleCat R) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      rw [ModuleCat.finrank_eq_zero_of_isZero
        (isZero_singularHomology_preimageSkeletonPair_of_lt hp R (Finset.mem_range.1 hi)),
        Nat.cast_zero, mul_zero]
  have hhigh : ∑ r ∈ Finset.range (N - (k + Q)), (-1 : ℤ) ^ (k + (Q + 1 + r)) *
      finrank R ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R)
        (k + (Q + 1 + r)) : ModuleCat R) = 0 :=
    Finset.sum_eq_zero fun r _ ↦ by
      rw [ModuleCat.finrank_eq_zero_of_isZero
        (isZero_singularHomology_preimageSkeletonPair_of_forall_cell hp R fun _ j ↦
          hzero j _ (by lia)), Nat.cast_zero, mul_zero]
  rw [hsplit, Finset.sum_range_add, hlow, zero_add, Finset.sum_range_add, hhigh, add_zero]
  have hterm (q : ℕ) (hq : q ∈ Finset.range (Q + 1)) :
      (-1 : ℤ) ^ (k + q) * finrank R
          ((preimageSkeletonPair p C k).singularHomology (ModuleCat.of R R) (k + q) : ModuleCat R) =
        ∑ j : cell C k, (-1 : ℤ) ^ k * ((-1 : ℤ) ^ q * finrank R
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (map k j 0)))) := by
    rw [Nat.add_comm k q, finrank_singularHomology_preimageSkeletonPair_add hp R k q
      fun j ↦ hfin j q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)),
      finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum, ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (N := Q + 1)
    fun q hq ↦ hzero j q (by lia)]

end SkeletonPair

section Relative

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u)

/-- Inclusion of the `n`-skeleton preimage pair `(p⁻¹(Xⁿ), p⁻¹(D))` into `(p⁻¹(C), p⁻¹(D))`. -/
abbrev preimageSkeletonLTToComplex (p : E ⟶ B) (C : Set B) {D : Set B} [RelCWComplex C D]
    (n : ℕ) :
    TopPair.ofInclusion (X := E)
        (preimage_mono (f := p) (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).base_subset) ⟶
      TopPair.ofInclusion (X := E) (preimage_mono (f := p) (base_subset_complex (C := C))) :=
  TopPair.ofInclusionMap _ _
    (ContinuousMap.inclusion
      (preimage_mono (f := p) (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex))
    fun _ hx ↦ hx

/-- The triple `(p⁻¹(C), p⁻¹(Xⁿ), p⁻¹(D))` comparing the `n`-skeleton preimage pair with the full
relative preimage pair `(p⁻¹(C), p⁻¹(D))`. -/
private abbrev skeletonToComplexTriple (p : E ⟶ B) (C : Set B) {D : Set B} [RelCWComplex C D]
    (n : ℕ) : TopTriple.{u} :=
  TopTriple.ofInclusions
    (preimage_mono (f := p) (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).base_subset)
    (preimage_mono (f := p) (skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex)

private lemma innerToTotal_skeletonToComplexTriple_eq (p : E ⟶ B) (C : Set B) {D : Set B}
    [RelCWComplex C D] (n : ℕ) :
    TopTriple.innerToTotal.app (skeletonToComplexTriple p C n) =
      preimageSkeletonLTToComplex p C n :=
  TopPair.hom_ext_of_fst _ (TopPair.ofInclusionMap_fst _ _).symm

include hp

/-- The outer pair `(p⁻¹(C), p⁻¹(Xⁿ))` of `skeletonToComplexTriple` has vanishing homology in all
degrees `m ≤ n`. -/
private theorem isZero_outerPair_skeletonToComplexTriple [Ring R] {n m : ℕ} (hm : m ≤ n) :
    IsZero ((TopTriple.outerPair.obj (skeletonToComplexTriple p C n)).singularHomology
      (ModuleCat.of R R) m) := by
  rw [TopTriple.outerPair_obj_ofInclusions,
    TopPair.ofInclusion_congr _
      (preimage_mono (f := p) (skeletonLT_mono (C := C) (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤)))
      rfl (by rw [skeletonLT_top])]
  exact isZero_singularHomology_preimage_skeletonLT hp R le_top hm

variable (C) in
/-- **Surjectivity from the `n`-skeleton preimage**: the inclusion
`(p⁻¹(Xⁿ), p⁻¹(D)) ⟶ (p⁻¹(C), p⁻¹(D))` induces an epimorphism on `Hₙ(-; R)`, with no dimension
bound on `C`. -/
theorem epi_singularHomologyMap_preimage_skeletonLT [Ring R] (n : ℕ) :
    Epi (TopPair.singularHomologyMap (preimageSkeletonLTToComplex p C n) (ModuleCat.of R R) n) := by
  rw [← innerToTotal_skeletonToComplexTriple_eq]
  exact ((skeletonToComplexTriple p C n).singularHomology_exact_total (ModuleCat.of R R) n).epi_f
    ((isZero_outerPair_skeletonToComplexTriple hp R le_rfl).eq_of_tgt _ _)

variable (C) in
/-- **Stabilization at the `(n + 1)`-skeleton preimage**: the inclusion
`(p⁻¹(Xⁿ), p⁻¹(D)) ⟶ (p⁻¹(C), p⁻¹(D))` induces an isomorphism on `Hₘ(-; R)` for every `m < n`,
with no dimension bound on `C`. -/
theorem isIso_singularHomologyMap_preimage_skeletonLT [Ring R] {n m : ℕ} (hm : m < n) :
    IsIso (TopPair.singularHomologyMap
      (preimageSkeletonLTToComplex p C n) (ModuleCat.of R R) m) := by
  rw [← innerToTotal_skeletonToComplexTriple_eq]
  exact (skeletonToComplexTriple p C n).isIso_singularHomologyMap_innerToTotal_of_isZero
    (ModuleCat.of R R) m (isZero_outerPair_skeletonToComplexTriple hp R hm.le)
    (isZero_outerPair_skeletonToComplexTriple hp R (Nat.succ_le_of_lt hm))

/-- Finiteness of `Hᵢ(p⁻¹(skeletonLT C n), p⁻¹(D); R)` over a Noetherian ring by induction on `n`.
-/
private theorem finite_singularHomology_preimage_skeletonLT_aux [Ring R] [IsNoetherianRing R]
    (n i : ℕ) (hcell : ∀ m < n, _root_.Finite (cell C m))
    (hfib : ∀ m < n, m ≤ i → ∀ j : cell C m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    Module.Finite R
      ((TopPair.ofInclusion (X := E)
        (preimage_mono (f := p) (skeletonLT C (n : ℕ∞)).base_subset)).singularHomology
          (ModuleCat.of R R) i : ModuleCat R) := by
  induction n with
  | zero =>
    have h0 : p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = p ⁻¹' D := by
      rw [Nat.cast_zero, skeletonLT_zero_eq_base]
    rw [TopPair.ofInclusion_congr
      (preimage_mono (f := p) (skeletonLT C ((0 : ℕ) : ℕ∞)).base_subset)
      (Subset.refl (p ⁻¹' D)) rfl h0]
    have : Subsingleton ((TopPair.ofInclusion (Subset.refl (p ⁻¹' D))).singularHomology
        (ModuleCat.of R R) i : ModuleCat R) :=
      ModuleCat.subsingleton_of_isZero
        (TopPair.isZero_singularHomology_ofInclusion_self (ModuleCat.of R R) (p ⁻¹' D) i)
    infer_instance
  | succ n ih =>
    let T := TopTriple.ofInclusions (X := E)
      (preimage_mono (f := p) (skeletonLT C (n : ℕ∞)).base_subset)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C n))
    have : Module.Finite R ((TopTriple.innerPair.obj T).singularHomology (ModuleCat.of R R) i :
        ModuleCat R) :=
      ih (fun m hm ↦ hcell m (hm.trans n.lt_succ_self))
        fun m hm ↦ hfib m (hm.trans n.lt_succ_self)
    have := hcell n n.lt_succ_self
    have : Module.Finite R ((TopTriple.outerPair.obj T).singularHomology (ModuleCat.of R R) i :
        ModuleCat R) :=
      finite_singularHomology_preimageSkeletonPair hp R n i (hfib n n.lt_succ_self)
    let g := (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) (ModuleCat.of R R) i).hom
    have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (T.singularHomology_exact_total (ModuleCat.of R R) i)
    exact Module.Finite.of_exact hexact.rangeRestrict g.surjective_rangeRestrict

/-- **Finiteness of relative homology of a Serre fibration over a CW pair.** Over a Noetherian
ring `R`, if `(C, D)` has finitely many cells in dimensions `m ≤ i` and the fibres over their
centres have finitely generated `H_{i - m}`, then `Hᵢ(p⁻¹(C), p⁻¹(D); R)` is finitely generated.
Neither `C` nor the fibres need be finite-dimensional. -/
theorem finite_singularHomology_preimage_base_subset_complex [Ring R] [IsNoetherianRing R] (i : ℕ)
    (hcell : ∀ m ≤ i, _root_.Finite (cell C m))
    (hfib : ∀ m ≤ i, ∀ j : cell C m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    Module.Finite R
      ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
        (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i : ModuleCat R) := by
  have := finite_singularHomology_preimage_skeletonLT_aux hp R (i + 1) i
    (fun m hm ↦ hcell m (Nat.lt_succ_iff.1 hm))
    (fun m hm _ ↦ hfib m (Nat.lt_succ_iff.1 hm))
  have hepi := epi_singularHomologyMap_preimage_skeletonLT C hp R i
  exact Module.Finite.of_surjective
    (TopPair.singularHomologyMap (preimageSkeletonLTToComplex p C i) (ModuleCat.of R R) i).hom
    ((ModuleCat.epi_iff_surjective _).1 hepi)

omit hp in
/-- Helper connecting `TopPair.ofInclusion` on `preimageSkeleton` at `-1` and `d - 1` to
`(p⁻¹(C), p⁻¹(D))` when there are no cells in dimensions `≥ d`. -/
private lemma ofInclusion_preimageSkeleton_neg_one_eq {d : ℕ}
    (hd : ∀ m, d ≤ m → IsEmpty (cell C m)) :
    TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (by lia : (-1 : ℤ) ≤ (d : ℤ) - 1)) =
      TopPair.ofInclusion (X := E) (preimage_mono (f := p) (base_subset_complex (C := C))) :=
  TopPair.ofInclusion_congr _ _ (preimageSkeleton_of_neg p (by lia)) (by
    rw [preimageSkeleton_def, show ((d : ℤ) - 1 + 1).toNat = d by lia,
      skeletonLT_eq_complex_of_isEmpty_cell C d hd])

/-- **Subadditivity of Betti numbers for a Serre fibration over a CW pair.** Over a division ring
`R`, if `(C, D)` has finitely many cells in dimensions `m ≤ i` and the fibres over their centres
have finite-dimensional `H_{i - m}`, then
`dim Hᵢ(p⁻¹(C), p⁻¹(D); R) ≤ ∑_{m ≤ i} ∑ⱼ dim H_{i - m}(p⁻¹(χⱼ(0)); R)`, with no dimension bound
on `C` or on the fibres. -/
theorem finrank_singularHomology_preimage_base_subset_complex_le [DivisionRing R] (i : ℕ)
    (hcell : ∀ m ≤ i, _root_.Finite (cell C m))
    (hfib : ∀ m ≤ i, ∀ j : cell C m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    finrank R ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
        (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i : ModuleCat R) ≤
      ∑ m ∈ Finset.range (i + 1), ∑ᶠ j : cell C m, finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  -- Surjectivity from the `i`-skeleton preimage reduces the bound to `preimageSkeleton` up to `i`.
  have := finite_singularHomology_preimage_skeletonLT_aux hp R (i + 1) i
    (fun m hm ↦ hcell m (Nat.lt_succ_iff.1 hm))
    (fun m hm _ ↦ hfib m (Nat.lt_succ_iff.1 hm))
  have hsurj := (ModuleCat.epi_iff_surjective _).1
    (epi_singularHomologyMap_preimage_skeletonLT C hp R i)
  let π := (TopPair.singularHomologyMap
    (preimageSkeletonLTToComplex p C i) (ModuleCat.of R R) i).hom
  have hπ : finrank R ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
      (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i : ModuleCat R) ≤
      finrank R ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p
        (by lia : (-1 : ℤ) ≤ i))).singularHomology (ModuleCat.of R R) i : ModuleCat R) := by
    have heq : TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (by lia : (-1 : ℤ) ≤ i)) =
        TopPair.ofInclusion (X := E)
          (preimage_mono (f := p) (skeletonLT C ((i + 1 : ℕ) : ℕ∞)).base_subset) :=
      TopPair.ofInclusion_congr _ _ (preimageSkeleton_of_neg p (by lia))
        (by rw [preimageSkeleton_def, show ((i : ℤ) + 1).toNat = i + 1 by lia])
    rw [heq, ← finrank_top R, ← LinearMap.range_eq_top.2 hsurj]
    exact LinearMap.finrank_range_le π
  refine hπ.trans
    (((monotone_preimageSkeleton (C := C) p).finrank_singularHomology_ofInclusion_le_sum
      (ModuleCat.of R R) (by lia) i fun b hb ↦ ?_).trans ?_)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, b = (m : ℤ) - 1 ∧ m ≤ i :=
      ⟨(b + 1).toNat, by rw [Finset.mem_Ico] at hb; lia⟩
    have := hcell m hm.2
    rw [ofInclusion_preimageSkeleton_eq_preimageSkeletonPair m b hm.1]
    exact finite_singularHomology_preimageSkeletonPair hp R m i fun _ ↦ hfib m hm.2
  · refine le_of_eq ((Finset.sum_bij (fun (b : ℤ) _ ↦ (b + 1).toNat)
      (fun b hb ↦ Finset.mem_range.2 (by rw [Finset.mem_Ico] at hb; lia))
      (fun b₁ hb₁ b₂ hb₂ h ↦ by rw [Finset.mem_Ico] at hb₁ hb₂; lia)
      (fun m hm ↦ ⟨(m : ℤ) - 1, Finset.mem_Ico.2 (by rw [Finset.mem_range] at hm; lia), by lia⟩)
      fun b hb ↦ ?_).trans rfl)
    have hbi : (b + 1).toNat ≤ i := by rw [Finset.mem_Ico] at hb; lia
    have := hcell (b + 1).toNat hbi
    rw [ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (b + 1).toNat b
      (by rw [Finset.mem_Ico] at hb; lia)]
    have hadd : i = i - (b + 1).toNat + (b + 1).toNat := (Nat.sub_add_cancel hbi).symm
    conv_lhs => rw [hadd]
    exact finrank_singularHomology_preimageSkeletonPair_add hp R (b + 1).toNat _ (hfib _ hbi)

/-- **Vanishing of relative homology above base plus fibre dimension.** Over any ring `R`, if
`(C, D)` has no cells of dimension `≥ d` and every cell-centre fibre has vanishing homology in
degrees `> Q`, then `Hᵢ(p⁻¹(C), p⁻¹(D); R) = 0` for all `i ≥ d + Q`. -/
theorem isZero_singularHomology_preimage_base_subset_complex_of_le [Ring R] {d Q i : ℕ}
    (hd : ∀ m, d ≤ m → IsEmpty (cell C m))
    (hzero : ∀ m < d, ∀ (j : cell C m) (q : ℕ), Q < q → IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hi : d + Q ≤ i) :
    IsZero ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
      (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i) := by
  suffices ∀ n ≤ d, IsZero ((TopPair.ofInclusion (X := E)
      (preimage_mono (f := p) (skeletonLT C (n : ℕ∞)).base_subset)).singularHomology
        (ModuleCat.of R R) i) by
    have hC : p ⁻¹' (skeletonLT C (d : ℕ∞) : Set B) = p ⁻¹' C := by
      rw [skeletonLT_eq_complex_of_isEmpty_cell C d hd]
    rw [← TopPair.ofInclusion_congr
      (preimage_mono (f := p) (skeletonLT C (d : ℕ∞)).base_subset) _ rfl hC]
    exact this d le_rfl
  intro n hn
  induction n with
  | zero =>
    have h0 : p ⁻¹' (skeletonLT C ((0 : ℕ) : ℕ∞) : Set B) = p ⁻¹' D := by
      rw [Nat.cast_zero, skeletonLT_zero_eq_base]
    rw [TopPair.ofInclusion_congr
      (preimage_mono (f := p) (skeletonLT C ((0 : ℕ) : ℕ∞)).base_subset)
      (Subset.refl (p ⁻¹' D)) rfl h0]
    exact TopPair.isZero_singularHomology_ofInclusion_self (ModuleCat.of R R) (p ⁻¹' D) i
  | succ n ih =>
    let T := TopTriple.ofInclusions (X := E)
      (preimage_mono (f := p) (skeletonLT C (n : ℕ∞)).base_subset)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C n))
    have hinner := ih (Nat.le_of_succ_le hn)
    have houter : IsZero ((TopTriple.outerPair.obj T).singularHomology (ModuleCat.of R R) i) :=
      isZero_singularHomology_preimageSkeletonPair_of_forall_cell hp R fun _ j ↦
        hzero n hn j (i - n) (by lia)
    exact T.isZero_singularHomology_totalPair (ModuleCat.of R R) i hinner houter

/-- **Eventual vanishing of relative homology of a Serre fibration over a finite CW pair.** Over
any ring `R`, if `(C, D)` is a finite relative CW complex and each cell-centre fibre has eventually
vanishing homology, then `Hᵢ(p⁻¹(C), p⁻¹(D); R)` vanishes for all sufficiently large `i`. -/
theorem eventually_isZero_singularHomology_preimage_base_subset_complex [Ring R]
    [RelCWComplex.Finite C]
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∀ᶠ i in Filter.atTop, IsZero ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
      (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i) := by
  obtain ⟨d, hd⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  have (m : Fin d) : _root_.Finite (cell C m) := FiniteType.finite_cell m
  have hall : ∀ᶠ Q in Filter.atTop, ∀ (m : Fin d) (j : cell C m),
      IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) Q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))) :=
    Filter.eventually_all.2 fun m ↦ Filter.eventually_all.2 fun j ↦ hzero m j
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hall
  refine Filter.eventually_atTop.2 ⟨d + Q, fun i hi ↦
    isZero_singularHomology_preimage_base_subset_complex_of_le hp R hd
      (fun m hm j q hq ↦ hQ q hq.le ⟨m, hm⟩ j) hi⟩

/-- **Euler's equality for a Serre fibration over a finite relative CW complex.** Over a division
ring `R`, if `(C, D)` is a finite relative CW complex and every cell-centre fibre has
finite-dimensional, eventually vanishing homology, then the alternating sum of dimensions of
`Hᵢ(p⁻¹(C), p⁻¹(D); R)` equals the cellwise alternating sum of the fibre Euler characteristics. -/
theorem finsum_finrank_singularHomology_preimage_base_subset_complex [DivisionRing R]
    [RelCWComplex.Finite C]
    (hfin : ∀ m (j : cell C m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
          (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i : ModuleCat R) =
      ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * ∑ᶠ j : cell C m, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  obtain ⟨d, hd⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  have hcell (m : ℕ) : _root_.Finite (cell C m) := FiniteType.finite_cell m
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 fun m : Fin d ↦
    Filter.eventually_all.2 fun j : cell C m ↦ hzero m j)
  have hzero' (m : ℕ) (hm : m < d) (j : cell C m) (q : ℕ) (hq : Q < q) :=
    hQ q hq.le ⟨m, hm⟩ j
  let F := monotone_preimageSkeleton (C := C) p
  -- Truncate the total-space `finsum` at `N + 1 = d + Q + 1` and apply Milnor's filtration formula.
  rw [ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (N := d + Q + 1) fun i hi ↦
      isZero_singularHomology_preimage_base_subset_complex_of_le hp R hd hzero' (by lia),
    ← ofInclusion_preimageSkeleton_neg_one_eq (p := p) hd,
    F.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq
      (ModuleCat.of R R) (by lia : (-1 : ℤ) ≤ (d : ℤ) - 1)
      (fun b hb i _ ↦ by
        rw [ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (b + 1).toNat b
          (by rw [Finset.mem_Ico] at hb; lia)]
        exact finite_singularHomology_preimageSkeletonPair hp R _ i fun _ j ↦ hfin _ j _)
      (fun b hb ↦ by
        rw [ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (b + 1).toNat b
          (by rw [Finset.mem_Ico] at hb; lia)]
        exact isZero_singularHomology_preimageSkeletonPair_of_forall_cell hp R fun _ j ↦
          hzero' (b + 1).toNat (by rw [Finset.mem_Ico] at hb; lia) j _
            (by rw [Finset.mem_Ico] at hb; lia))]
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := Finset.range (d + Q + 1))]
  -- Reindex `b ∈ Ico (-1) (d - 1)` by cell dimension `m ∈ range d` and evaluate each step.
  have hsteps : ∑ b ∈ Finset.Ico (-1 : ℤ) ((d : ℤ) - 1), ∑ i ∈ Finset.range (d + Q + 1),
        (-1 : ℤ) ^ i * finrank R ((TopPair.ofInclusion (F
          (lt_add_one b).le)).singularHomology (ModuleCat.of R R) i : ModuleCat R) =
      ∑ m ∈ Finset.range d, (-1 : ℤ) ^ m * ∑ᶠ j : cell C m, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q *
        finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) :=
    Finset.sum_bij (fun (b : ℤ) _ ↦ (b + 1).toNat)
      (fun b hb ↦ Finset.mem_range.2 (by rw [Finset.mem_Ico] at hb; lia))
      (fun b₁ hb₁ b₂ hb₂ h ↦ by rw [Finset.mem_Ico] at hb₁ hb₂; lia)
      (fun m hm ↦ ⟨(m : ℤ) - 1, Finset.mem_Ico.2 (by rw [Finset.mem_range] at hm; lia), by lia⟩)
      fun b hb ↦ by
        have hbm : (b + 1).toNat < d := by rw [Finset.mem_Ico] at hb; lia
        rw [ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (b + 1).toNat b
          (by rw [Finset.mem_Ico] at hb; lia)]
        exact sum_range_neg_one_pow_mul_finrank_singularHomology_preimageSkeletonPair hp R
          (Q := Q) (by lia) (fun j q _ ↦ hfin _ j q) (hzero' _ hbm)
  rw [hsteps, eq_comm]
  refine finsum_eq_sum_of_support_subset _ fun m hm ↦ ?_
  by_contra hmd
  have := hd m (by simpa using hmd)
  exact hm (by simp [finsum_of_isEmpty])

/-- **Multiplicativity of the Euler characteristic for a Serre fibration over a finite relative CW
complex.** If every cell-centre fibre has finite-dimensional, eventually vanishing homology over a
division ring `R` with alternating dimension sum `c`, then the alternating dimension sum of
`Hᵢ(p⁻¹(C), p⁻¹(D); R)` is `cwEulerChar C · c`. -/
theorem finsum_finrank_singularHomology_preimage_base_subset_complex_of_eq [DivisionRing R]
    [RelCWComplex.Finite C] {c : ℤ}
    (hfin : ∀ m (j : cell C m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hc : ∀ m (j : cell C m), ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        ((TopPair.ofInclusion (X := E) (preimage_mono (f := p)
          (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i : ModuleCat R) =
      cwEulerChar C * c := by
  rw [finsum_finrank_singularHomology_preimage_base_subset_complex hp R hfin hzero,
    cwEulerChar_def, finsum_mul]
  refine finsum_congr fun m ↦ ?_
  have := FiniteType.finite_cell (C := C) (D := D) m
  cases nonempty_fintype (cell C m)
  simp_rw [hc m, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_assoc]

end Relative

section Absolute

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] (hp : serreFibrations p) (R : Type u)

/-- Isomorphism `Hᵢ(p⁻¹(C); R) ≅ Hᵢ(p⁻¹(C), p⁻¹(∅); R)` for an absolute CW complex `C`. -/
private def singularHomologyPreimageIsoPair (C : Set B) [CWComplex C] [Ring R] (i : ℕ) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) ≅
      (TopPair.ofInclusion (X := E) (preimage_mono (f := p)
        (base_subset_complex (C := C)))).singularHomology (ModuleCat.of R R) i := by
  let P := TopPair.ofInclusion (X := E) (preimage_mono (f := p) (base_subset_complex (C := C)))
  have : IsEmpty P.snd := ⟨fun x ↦ x.2⟩
  have hπ : IsIso (P.singularHomologyπ (C := ModuleCat.{u} R) (ModuleCat.of R R) i) := inferInstance
  exact @asIso _ _ _ _ _ hπ

/-- Isomorphism `Hᵢ(E; R) ≅ Hᵢ(p⁻¹(univ); R)`. -/
private def singularHomologyIsoPreimageUniv [Ring R] (i : ℕ) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj E) ≅
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' (univ : Set B)))) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
    (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo
      ((Homeomorph.setCongr (preimage_univ (f := p))).trans (Homeomorph.Set.univ E))).symm)

include hp

/-- **Finiteness of preimage homology** of a Serre fibration over an absolute CW complex `C` with
finitely many cells through degree `i`, over any Noetherian ring `R`. -/
theorem finite_singularHomology_preimage_of_cwComplex (C : Set B) [CWComplex C] [Ring R]
    [IsNoetherianRing R] (i : ℕ) (hcell : ∀ m ≤ i, _root_.Finite (cell C m))
    (hfib : ∀ m ≤ i, ∀ j : cell C m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    Module.Finite R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) :=
  have := finite_singularHomology_preimage_base_subset_complex (C := C) hp R i hcell hfib
  Module.Finite.equiv (singularHomologyPreimageIsoPair (p := p) R C i).symm.toLinearEquiv

/-- **Subadditivity of Betti numbers** for the preimage `p⁻¹(C)` of an absolute CW complex `C`
under a Serre fibration, over a division ring `R`. -/
theorem finrank_singularHomology_preimage_of_cwComplex_le (C : Set B) [CWComplex C]
    [DivisionRing R] (i : ℕ) (hcell : ∀ m ≤ i, _root_.Finite (cell C m))
    (hfib : ∀ m ≤ i, ∀ j : cell C m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) ≤
      ∑ m ∈ Finset.range (i + 1), ∑ᶠ j : cell C m, finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  rw [(singularHomologyPreimageIsoPair (p := p) R C i).toLinearEquiv.finrank_eq]
  exact finrank_singularHomology_preimage_base_subset_complex_le hp R i hcell hfib

/-- **Eventual vanishing of preimage homology** of a Serre fibration over a finite CW complex `C`,
over any ring `R`. -/
theorem eventually_isZero_singularHomology_preimage_of_finite_cwComplex (C : Set B) [CWComplex C]
    [RelCWComplex.Finite C] [Ring R]
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∀ᶠ i in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) :=
  (eventually_isZero_singularHomology_preimage_base_subset_complex (C := C) hp R hzero).mono
    fun i hi ↦ hi.of_iso (singularHomologyPreimageIsoPair (p := p) R C i)

/-- **Cellwise Euler's equality** for the preimage `p⁻¹(C)` of a finite CW complex `C` under a
Serre fibration, over a division ring `R`. -/
theorem finsum_finrank_singularHomology_preimage_of_finite_cwComplex (C : Set B) [CWComplex C]
    [RelCWComplex.Finite C] [DivisionRing R]
    (hfin : ∀ m (j : cell C m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
           (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) =
      ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * ∑ᶠ j : cell C m, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  simp_rw [(singularHomologyPreimageIsoPair (p := p) R C _).toLinearEquiv.finrank_eq]
  exact finsum_finrank_singularHomology_preimage_base_subset_complex hp R hfin hzero

/-- **Multiplicativity of the Euler characteristic** on the preimage `p⁻¹(C)` of a finite CW
complex `C` under a Serre fibration: when every cell-centre fibre has alternating homology dimension
sum `c` over a division ring `R`, `p⁻¹(C)` has alternating homology dimension sum
`cwEulerChar C · c`. -/
theorem finsum_finrank_singularHomology_preimage_of_finite_cwComplex_of_eq (C : Set B)
    [CWComplex C] [RelCWComplex.Finite C] [DivisionRing R] {c : ℤ}
    (hfin : ∀ m (j : cell C m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell C m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hc : ∀ m (j : cell C m), ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
          (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' C))) =
      cwEulerChar C * c := by
  simp_rw [(singularHomologyPreimageIsoPair (p := p) R C _).toLinearEquiv.finrank_eq]
  exact finsum_finrank_singularHomology_preimage_base_subset_complex_of_eq hp R hfin hzero hc

/-- **Finiteness of total-space homology** of a Serre fibration over a CW complex `(univ : Set B)`
of finite type through degree `i`, over any Noetherian ring `R`. -/
theorem finite_singularHomology_of_cwComplex_univ [CWComplex (univ : Set B)] [Ring R]
    [IsNoetherianRing R] (i : ℕ) (hcell : ∀ m ≤ i, _root_.Finite (cell (univ : Set B) m))
    (hfib : ∀ m ≤ i, ∀ j : cell (univ : Set B) m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    Module.Finite R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj E) :=
  have := finite_singularHomology_preimage_of_cwComplex hp R (univ : Set B) i hcell hfib
  Module.Finite.equiv (singularHomologyIsoPreimageUniv (p := p) R i).symm.toLinearEquiv

/-- **Subadditivity of Betti numbers** for the total space `E` of a Serre fibration over a CW
complex `(univ : Set B)`, over a division ring `R`. -/
theorem finrank_singularHomology_of_cwComplex_univ_le [CWComplex (univ : Set B)] [DivisionRing R]
    (i : ℕ) (hcell : ∀ m ≤ i, _root_.Finite (cell (univ : Set B) m))
    (hfib : ∀ m ≤ i, ∀ j : cell (univ : Set B) m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj E) ≤
      ∑ m ∈ Finset.range (i + 1), ∑ᶠ j : cell (univ : Set B) m, finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  rw [(singularHomologyIsoPreimageUniv (p := p) R i).toLinearEquiv.finrank_eq]
  exact finrank_singularHomology_preimage_of_cwComplex_le hp R (univ : Set B) i hcell hfib

/-- **Eventual vanishing of total-space homology** of a Serre fibration over a finite CW complex
`(univ : Set B)`, over any ring `R`. -/
theorem eventually_isZero_singularHomology_of_finite_cwComplex_univ [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] [Ring R]
    (hzero : ∀ m (j : cell (univ : Set B) m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∀ᶠ i in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj E) :=
  (eventually_isZero_singularHomology_preimage_of_finite_cwComplex hp R (univ : Set B) hzero).mono
    fun i hi ↦ hi.of_iso (singularHomologyIsoPreimageUniv (p := p) R i)

/-- **Cellwise Euler's equality** for a Serre fibration over a finite CW complex `(univ : Set B)`,
over a division ring `R`. -/
theorem finsum_finrank_singularHomology_of_finite_cwComplex_univ [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] [DivisionRing R]
    (hfin : ∀ m (j : cell (univ : Set B) m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell (univ : Set B) m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0)))) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
           (ModuleCat.of R R)).obj E) =
      ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * ∑ᶠ j : cell (univ : Set B) m, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (map m j 0))) := by
  simp_rw [(singularHomologyIsoPreimageUniv (p := p) R _).toLinearEquiv.finrank_eq]
  exact finsum_finrank_singularHomology_preimage_of_finite_cwComplex hp R (univ : Set B) hfin hzero

/-- **Multiplicativity of the Euler characteristic** for a Serre fibration over a finite CW complex
`(univ : Set B)`: when every cell-centre fibre has alternating homology dimension sum `c` over a
division ring `R`, the total space has alternating homology dimension sum
`cwEulerChar (univ : Set B) · c`. -/
theorem finsum_finrank_singularHomology_of_finite_cwComplex_univ_of_eq [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] [DivisionRing R] {c : ℤ}
    (hfin : ∀ m (j : cell (univ : Set B) m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hzero : ∀ m (j : cell (univ : Set B) m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))))
    (hc : ∀ m (j : cell (univ : Set B) m), ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (map m j 0))) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
          (ModuleCat.of R R)).obj E) =
      cwEulerChar (univ : Set B) * c := by
  simp_rw [(singularHomologyIsoPreimageUniv (p := p) R _).toLinearEquiv.finrank_eq]
  exact finsum_finrank_singularHomology_preimage_of_finite_cwComplex_of_eq hp R (univ : Set B) hfin
    hzero hc

end Absolute

section Pullback

variable {E B B' : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u)
  [T2Space B'] [CWComplex (univ : Set B')] {g : B' ⟶ B} (hg : g.hom.IsWeakHomotopyEquivalence)

include hp hg

/-- Isomorphism `Hᵢ(B' ×_B E; R) ≅ Hᵢ(E; R)` induced by the base change of a Serre fibration along
a weak homotopy equivalence `g : B' ⟶ B`. -/
private def pullbackTotalSingularHomologyIso [Ring R] (i : ℕ) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of { x : B' × E // g x.1 = p x.2 })) ≅
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj E) :=
  have := (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap
    (ModuleCat.of R R) i
  asIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
    (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd g p))

/-- **Finiteness of total-space homology along a CW approximation or model.** Let `p : E ⟶ B` be a
Serre fibration and `g : B' ⟶ B` a weak homotopy equivalence from a CW complex `(univ : Set B')`
with finitely many cells through degree `i`. Over a Noetherian ring `R`, if the fibres of `p` over
the images of those cell centres have finitely generated `H_{i - m}`, then `Hᵢ(E; R)` is finitely
generated. -/
theorem finite_singularHomology_of_isWeakHomotopyEquivalence [Ring R] [IsNoetherianRing R] (i : ℕ)
    (hcell : ∀ m ≤ i, _root_.Finite (cell (univ : Set B') m))
    (hfib : ∀ m ≤ i, ∀ j : cell (univ : Set B') m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0))))) :
    Module.Finite R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R R)).obj E) := by
  have := finite_singularHomology_of_cwComplex_univ (mem_serreFibrations_pullbackFst hp g) R i
    hcell fun m hm j ↦ by
      have := hfib m hm j
      exact Module.Finite.equiv (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
        (i - m)).obj (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))
          ).symm.toLinearEquiv
  exact Module.Finite.equiv (pullbackTotalSingularHomologyIso hp R hg i).toLinearEquiv

/-- **Subadditivity of Betti numbers along a CW approximation or model.** Let `p : E ⟶ B` be a Serre
fibration and `g : B' ⟶ B` a weak homotopy equivalence from a CW complex `(univ : Set B')` with
finitely many cells through degree `i`. Over a division ring `R`, if the fibres of `p` over the
images of those cell centres have finite-dimensional `H_{i - m}`, then
`dim Hᵢ(E; R) ≤ ∑_{m ≤ i} ∑ⱼ dim H_{i - m}(p⁻¹(g(χⱼ(0))); R)`. -/
theorem finrank_singularHomology_of_isWeakHomotopyEquivalence_le [DivisionRing R] (i : ℕ)
    (hcell : ∀ m ≤ i, _root_.Finite (cell (univ : Set B') m))
    (hfib : ∀ m ≤ i, ∀ j : cell (univ : Set B') m, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0))))) :
    finrank R (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj E) ≤
      ∑ m ∈ Finset.range (i + 1), ∑ᶠ j : cell (univ : Set B') m, finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
          (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))) := by
  rw [← (pullbackTotalSingularHomologyIso hp R hg i).toLinearEquiv.finrank_eq]
  refine (finrank_singularHomology_of_cwComplex_univ_le
    (mem_serreFibrations_pullbackFst hp g) R i hcell fun m hm j ↦ ?_).trans_eq ?_
  · have := hfib m hm j
    exact Module.Finite.equiv (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
      (i - m)).obj (ModuleCat.of R R)).mapIso
        (p.fiberPullbackFstIso g (map m j 0))).symm.toLinearEquiv
  · refine Finset.sum_congr rfl fun m _ ↦ finsum_congr fun j ↦ ?_
    exact (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (i - m)).obj
      (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))).toLinearEquiv.finrank_eq

/-- **Eventual vanishing of total-space homology along a finite CW model.** Let `p : E ⟶ B` be a
Serre fibration and `g : B' ⟶ B` a weak homotopy equivalence from a finite CW complex
`(univ : Set B')`. Over any ring `R`, if the fibres of `p` over the images of cell centres have
eventually vanishing homology, then `Hᵢ(E; R)` vanishes for all sufficiently large `i`. -/
theorem eventually_isZero_singularHomology_of_isWeakHomotopyEquivalence
    [RelCWComplex.Finite (univ : Set B')] [Ring R]
    (hzero : ∀ m (j : cell (univ : Set B') m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0))))) :
    ∀ᶠ i in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
        (ModuleCat.of R R)).obj E) :=
  (eventually_isZero_singularHomology_of_finite_cwComplex_univ
    (mem_serreFibrations_pullbackFst hp g) R fun m j ↦ (hzero m j).mono fun q hq ↦
      hq.of_iso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0)))).mono fun i hi ↦
    hi.of_iso (pullbackTotalSingularHomologyIso hp R hg i).symm

/-- **Cellwise Euler's equality along a finite CW model.** Let `p : E ⟶ B` be a Serre fibration
and `g : B' ⟶ B` a weak homotopy equivalence from a finite CW complex `(univ : Set B')`. Over a
division ring `R`, if the fibres of `p` over the images of cell centres have finite-dimensional,
eventually vanishing homology, then the alternating dimension sum of `Hᵢ(E; R)` equals the cellwise
alternating sum of the Euler characteristics of those fibres. -/
theorem finsum_finrank_singularHomology_of_isWeakHomotopyEquivalence
    [RelCWComplex.Finite (univ : Set B')] [DivisionRing R]
    (hfin : ∀ m (j : cell (univ : Set B') m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))))
    (hzero : ∀ m (j : cell (univ : Set B') m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0))))) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
           (ModuleCat.of R R)).obj E) =
      ∑ᶠ m : ℕ, (-1 : ℤ) ^ m * ∑ᶠ j : cell (univ : Set B') m, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))) := by
  simp_rw [← (pullbackTotalSingularHomologyIso hp R hg _).toLinearEquiv.finrank_eq]
  rw [finsum_finrank_singularHomology_of_finite_cwComplex_univ
    (mem_serreFibrations_pullbackFst hp g) R
    (fun m j q ↦ by
      have := hfin m j q
      exact Module.Finite.equiv (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
        q).obj (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))).symm.toLinearEquiv)
    (fun m j ↦ (hzero m j).mono fun q hq ↦ hq.of_iso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))))]
  refine finsum_congr fun m ↦ congrArg _ (finsum_congr fun j ↦ finsum_congr fun q ↦
    congrArg (fun d : ℕ ↦ (-1 : ℤ) ^ q * (d : ℤ)) ?_)
  exact (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
    (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))).toLinearEquiv.finrank_eq

/-- **Multiplicativity of the Euler characteristic along a finite CW model.** Let `p : E ⟶ B` be a
Serre fibration and `g : B' ⟶ B` a weak homotopy equivalence from a finite CW complex
`(univ : Set B')`. Over a division ring `R`, if every cell-centre fibre `p⁻¹(g(χⱼ(0)))` has
finite-dimensional, eventually vanishing homology with alternating dimension sum `c`, then
`∑ᶠ i, (-1)ⁱ dim Hᵢ(E; R) = cwEulerChar (univ : Set B') · c`. -/
theorem finsum_finrank_singularHomology_of_isWeakHomotopyEquivalence_of_eq
    [RelCWComplex.Finite (univ : Set B')] [DivisionRing R] {c : ℤ}
    (hfin : ∀ m (j : cell (univ : Set B') m) q, Module.Finite R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))))
    (hzero : ∀ m (j : cell (univ : Set B') m), ∀ᶠ q in Filter.atTop, IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))))
    (hc : ∀ m (j : cell (univ : Set B') m), ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * finrank R
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber (g (map m j 0)))) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) i).obj
          (ModuleCat.of R R)).obj E) =
      cwEulerChar (univ : Set B') * c := by
  simp_rw [← (pullbackTotalSingularHomologyIso hp R hg _).toLinearEquiv.finrank_eq]
  exact finsum_finrank_singularHomology_of_finite_cwComplex_univ_of_eq
    (mem_serreFibrations_pullbackFst hp g) R
    (fun m j q ↦ by
      have := hfin m j q
      exact Module.Finite.equiv (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
        q).obj (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))).symm.toLinearEquiv)
    (fun m j ↦ (hzero m j).mono fun q hq ↦ hq.of_iso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map m j 0))))
    fun m j ↦ (finsum_congr fun q ↦ congrArg (fun d : ℕ ↦ (-1 : ℤ) ^ q * (d : ℤ))
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).mapIso
          (p.fiberPullbackFstIso g (map m j 0))).toLinearEquiv.finrank_eq)).trans (hc m j)

end Pullback

end TopCat

end TauCeti

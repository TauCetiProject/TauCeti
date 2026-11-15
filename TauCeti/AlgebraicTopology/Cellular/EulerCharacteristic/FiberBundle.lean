/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ComplexShape
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.Topology.Category.TopCat.Fiber
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
import TauCeti.Algebra.Homology.SpectralSequence.EulerCharacteristic
import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase
import TauCeti.Topology.CWComplex.Comparison
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# Multiplicativity of the Euler characteristic in Serre fibrations and fibre bundles

Let `p : E ⟶ B` be a Serre fibration whose base `B` and fibres `p⁻¹(b)` have finite CW type. Pulling
`p` back along a homotopy equivalence `B' ≃ₕ B` from a finite CW complex `B'` (`univ : Set B'`)
reduces `p` to a Serre fibration `p' : B' ×_B E ⟶ B'` over `B'` whose Serre spectral sequence
(`TauCeti.TopCat.serreSpectralSequence`) converges strongly to `H_*(E; R)`
(`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`). On its initial page (numbered `2`), the
term at bidegree `(1 - q - 2d, d - 1)` is `⨁_{j : cell B' d} H_q(p'⁻¹(χ_j(0)); R)`
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`), while all other bidegrees vanish.

Even when `B` is disconnected or not simply connected and monodromy acts nontrivially on fibre
homology, the initial page is concentrated in finitely many bidegrees, and over a division ring `k`
its `d`-cell summand contributes `(-1)^d · χ(p'⁻¹(χ_j(0)))` regardless of differentials. Page
invariance of the Euler characteristic
(`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le`) and strong convergence
(`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment`) pass this
alternating sum unchanged through the `E²` page (`r = 3`) and every higher page to the singular
homology of `E`. No finite CW structure on `E` and no triviality of the monodromy action are
assumed.

Specializing to a fibre bundle `FiberBundle F E` via `TauCeti.TopCat.mem_serreFibrations_proj` and
local trivializations gives `∑ᶠ i, (-1)^i dim_k H_i(TotalSpace F E; k) = χ(B) · χ(F)`
(`TauCeti.finsum_finrank_singularHomology_fiberBundle`), and hence
`χ(TotalSpace F E) = χ(B) · χ(F)` whenever the total space also has finite CW type
(`TauCeti.eulerChar_totalSpace_fiberBundle`).

## Main results

* `TauCeti.TopCat.eulerChar_serreSpectralSequence_page`: over a finite CW base `B`, every page
  `r ≥ 2` of the Serre spectral sequence of `p` over a division ring `k` has Euler characteristic
  `∑ᶠ d, (-1)^d ∑ᶠ j : cell B d, χ(p⁻¹(χ_j(0)))`.
* `TauCeti.TopCat.finite_singularHomology_of_mem_serreFibrations` and
  `TauCeti.TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations`: over a base and fibres
  of finite CW type, `H_n(E; R)` is finitely generated in every degree (for Noetherian `R`) and
  vanishes in all sufficiently large degrees (for any ring `R`).
* `TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations` and
  `TauCeti.TopCat.eulerChar_eq_mul_of_mem_serreFibrations`: when every fibre has Euler
  characteristic `c`, the alternating sum of Betti numbers of `E` over `k` (and `χ(E)` when `E` has
  finite CW type) equals `χ(B) · c`.
* `TauCeti.finite_singularHomology_fiberBundle`,
  `TauCeti.eventually_isZero_singularHomology_fiberBundle`,
  `TauCeti.finsum_finrank_singularHomology_fiberBundle`, and
  `TauCeti.eulerChar_totalSpace_fiberBundle`: finiteness, eventual vanishing, and multiplicativity
  of the Euler characteristic for fibre bundles with base and fibre of finite CW type.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II, §3, Proposition 4.
* J. R. Klein, C. Malkiewich, M. Ramzi, *Euler characteristic of fibrations*, pp. 1–2.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 1.15 and Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Bundle Topology Topology.RelCWComplex AlgebraicTopology

universe u

namespace TauCeti

/-! ### Coproduct and sign helpers -/

section CoproductHelpers

private lemma isZero_sigmaObj {R : Type u} [Ring R] {ι : Type u} (Z : ι → ModuleCat.{u} R)
    (h : ∀ i, IsZero (Z i)) : IsZero (∐ Z) :=
  (IsZero.iff_id_eq_zero _).2 <| Sigma.hom_ext _ _ fun i ↦ (h i).eq_of_src _ _

private lemma finite_sigmaObj {R : Type u} [Ring R] {ι : Type u} [_root_.Finite ι]
    (Z : ι → ModuleCat.{u} R) (h : ∀ i, Module.Finite R (Z i)) :
    Module.Finite R ↥(∐ Z) := by
  classical
  let _ := Fintype.ofFinite ι
  have := h
  exact .equiv (ModuleCat.coprodIsoDirectSum Z).toLinearEquiv.symm

private lemma finrank_sigmaObj {k : Type u} [DivisionRing k] {ι : Type u} [Fintype ι]
    (Z : ι → ModuleCat.{u} k) [∀ i, Module.Finite k (Z i)] :
    finrank k ↥(∐ Z) = ∑ i : ι, finrank k (Z i) := by
  classical
  rw [(ModuleCat.coprodIsoDirectSum Z).toLinearEquiv.finrank_eq, Module.finrank_directSum]

private lemma coe_negOnePow_neg_natCast (n : ℕ) :
    (((-(n : ℤ)).negOnePow : ℤˣ) : ℤ) = (-1 : ℤ) ^ n := by
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]

/-- Bidegree `(1 - q - 2d, d - 1)` on page `2` of `serreSpectralSequence` corresponding to base
cell dimension `d` and fibre homology degree `q`. -/
private def serreBideg (d q : ℕ) : ℤ × ℤ :=
  (1 - (q : ℤ) - 2 * (d : ℤ), (d : ℤ) - 1)

private lemma serreBideg_injective : Function.Injective2 serreBideg := by
  intro d₁ q₁ d₂ q₂ h
  simp only [serreBideg, Prod.mk.injEq] at h
  lia

end CoproductHelpers

namespace TopCat

/-! ### Serre spectral sequence over a finite CW base -/

/-- Below row `b = -1`, both skeletal preimages `E_b` and `E_{b+1}` over a CW complex `K` are
empty, so page `2` of the Serre spectral sequence vanishes for `pq.2 < -1`. -/
private lemma isZero_serreSpectralSequence_page_two_X_of_lt_neg_one
    {E B : _root_.TopCat.{u}} (R : Type u) [Ring R] [T2Space B]
    (K : Set B) [CWComplex K] (p : E ⟶ B) (pq : ℤ × ℤ) (hb : pq.2 < -1) :
    IsZero (((serreSpectralSequence K p R).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hneg
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ -(pq.1 + pq.2))
    have hpair : IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := K) p
        (Int.le_add_one le_rfl) : preimageSkeleton K p pq.2 ⊆
          preimageSkeleton K p (pq.2 + 1))).singularHomology (ModuleCat.of R R) n) :=
      (TopPair.isZero_singularHomology_ofInclusion_congr (ModuleCat.of R R) _
        (subset_refl (∅ : Set E)) (preimageSkeleton_eq_empty p (by lia))
        (preimageSkeleton_eq_empty p (by lia)) n).2
        (TopPair.isZero_singularHomology_ofInclusion_self (ModuleCat.of R R) (∅ : Set E) n)
    exact hpair.of_iso (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
      (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n (by lia))

section CWBase

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  [T2Space B] [CWComplex (univ : Set B)]

omit [T2Space B] in
/-- Uniform dimension bound `D` on the cells of `B` together with a uniform degree bound `Q` above
which the homology of every cell-centre fibre `p⁻¹(χ_j(0))` vanishes. -/
private lemma exists_cell_and_fiber_vanishing_bounds (p : E ⟶ B) (R : Type u) [Ring R]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] :
    ∃ D Q : ℕ, (∀ d ≥ D, IsEmpty (cell (univ : Set B) d)) ∧
      ∀ d < D, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
        IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (p.fiber (map d j 0))) := by
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := (univ : Set B)) (D := ∅))
  have hbound : ∀ (d : Fin D) (j : cell (univ : Set B) d.1), ∃ Q : ℕ, ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d.1 j 0))) := fun d j ↦
    Filter.eventually_atTop.1
      (eventually_isZero_singularHomology_of_finiteCWType (p.fiber (map d.1 j 0))
        (ModuleCat.of R R))
  choose Qfn hQfn using hbound
  have : ∀ d : Fin D, _root_.Finite (cell (univ : Set B) d.1) := fun d ↦ FiniteType.finite_cell d.1
  let _ := Fintype.ofFinite (Σ d : Fin D, cell (univ : Set B) d.1)
  refine ⟨D, Finset.univ.sup (fun dj : Σ d : Fin D, cell (univ : Set B) d.1 ↦ Qfn dj.1 dj.2),
    hD, fun d hd j q hq ↦ hQfn ⟨d, hd⟩ j q ?_⟩
  exact (Finset.le_sup (f := fun dj : Σ d : Fin D, cell (univ : Set B) d.1 ↦ Qfn dj.1 dj.2)
    (Finset.mem_univ ⟨⟨d, hd⟩, j⟩)).trans hq

include hp in
/-- Given cell and fibre vanishing bounds `(D, Q)` on `B`, page `2` of the Serre spectral sequence
of `p : E ⟶ B` vanishes outside `image serreBideg (range D ×ˢ range Q)`. -/
private lemma isZero_serreSpectralSequence_page_two_X_of_notMem (R : Type u) [Ring R] {D Q : ℕ}
    (hD : ∀ d ≥ D, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < D, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d j 0))))
    {pq : ℤ × ℤ}
    (hpq : pq ∉ (Finset.range D ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2) :
    IsZero (((serreSpectralSequence (univ : Set B) p R).page 2).X pq) := by
  by_cases hb : pq.2 < -1
  · exact isZero_serreSpectralSequence_page_two_X_of_lt_neg_one R univ p pq hb
  · by_cases hq : 0 ≤ pq.1 + 2 * pq.2
    · exact isZero_serreSpectralSequence_page_two_X hp R univ pq hq
    · set d := (pq.2 + 1).toNat
      set q := (-pq.1 - 2 * pq.2 - 1).toNat
      have hpq_eq : pq = serreBideg d q := by ext <;> simp only [serreBideg] <;> lia
      refine (isZero_sigmaObj _ fun j ↦ ?_).of_iso
        (serreSpectralSequenceFirstPageXIsoSigma (univ : Set B) hp R d q pq (by lia) (by lia))
      rcases lt_or_ge d D with hdD | hdD
      · refine hQ d hdD j q ?_
        by_contra hlt
        exact hpq (Finset.mem_image.2 ⟨(d, q),
          Finset.mem_product.2 ⟨Finset.mem_range.2 hdD, Finset.mem_range.2 (by lia)⟩,
          hpq_eq.symm⟩)
      · exact (hD d hdD).elim j

include hp in
/-- Over a finite CW complex `B` and a Noetherian ring `R`, every term on page `2` of the Serre
spectral sequence of `p : E ⟶ B` is finitely generated once all fibres have finite CW type. -/
private lemma finite_serreSpectralSequence_page_two_X (R : Type u) [Ring R] [IsNoetherianRing R]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] (pq : ℤ × ℤ) :
    Module.Finite R (((serreSpectralSequence (univ : Set B) p R).page 2).X pq) := by
  by_cases hb : pq.2 < -1
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_serreSpectralSequence_page_two_X_of_lt_neg_one R univ p pq hb)
    infer_instance
  · by_cases hq : 0 ≤ pq.1 + 2 * pq.2
    · have := ModuleCat.subsingleton_of_isZero
        (isZero_serreSpectralSequence_page_two_X hp R univ pq hq)
      infer_instance
    · set d := (pq.2 + 1).toNat
      set q := (-pq.1 - 2 * pq.2 - 1).toNat
      have : _root_.Finite (cell (univ : Set B) d) := FiniteType.finite_cell d
      have : Module.Finite R ↥(∐ fun j : cell (univ : Set B) d ↦
          ((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
            (p.fiber (map d j 0))) :=
        finite_sigmaObj _ fun j ↦
          finite_singularHomology_of_finiteCWType (p.fiber (map d j 0)) (ModuleCat.of R R) q
      exact .equiv (serreSpectralSequenceFirstPageXIsoSigma (univ : Set B) hp R d q pq
        (by lia) (by lia)).symm.toLinearEquiv

include hp in
/-- Over a finite CW complex `B` and a division ring `k`, the Euler characteristic of page `2` of
the Serre spectral sequence is the alternating sum over `range D` of the cell-centre fibre Euler
characteristics. -/
private lemma eulerChar_serreSpectralSequence_page_two_eq_sum_range (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] {D Q : ℕ}
    (hD : ∀ d ≥ D, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < D, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (map d j 0)))) :
    ((serreSpectralSequence (univ : Set B) p k).page 2).eulerChar =
      ∑ d ∈ Finset.range D, (-1 : ℤ) ^ d *
        ∑ᶠ j : cell (univ : Set B) d, eulerChar (p.fiber (map d j 0)) := by
  let S : Finset (ℤ × ℤ) := (Finset.range D ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2
  rw [((serreSpectralSequence (univ : Set B) p k).page
      2).eulerChar_eq_sum_finSet_of_finrankSupport_subset S
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
        ModuleCat.finrank_eq_zero_of_isZero
          (isZero_serreSpectralSequence_page_two_X_of_notMem hp k hD hQ hpq)),
    Finset.sum_image (fun dq₁ _ dq₂ _ h ↦ Prod.ext
      (serreBideg_injective h).1 (serreBideg_injective h).2), Finset.sum_product]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have : _root_.Finite (cell (univ : Set B) d) := FiniteType.finite_cell d
  let _ := Fintype.ofFinite (cell (univ : Set B) d)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  calc
    ∑ q ∈ Finset.range Q,
        (((ComplexShape.up' (⟨2, 1 - 2⟩ : ℤ × ℤ)).χ (serreBideg d q) : ℤ) *
          finrank k (((serreSpectralSequence (univ : Set B) p k).page 2).X (serreBideg d q)))
      = ∑ q ∈ Finset.range Q, ∑ j : cell (univ : Set B) d,
          (-1 : ℤ) ^ d * ((-1 : ℤ) ^ q * finrank k
            (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
              (p.fiber (map d j 0)))) := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        have (j : cell (univ : Set B) d) :
            Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) q).obj
              (ModuleCat.of k k)).obj (p.fiber (map d j 0))) :=
          finite_singularHomology_of_finiteCWType (p.fiber (map d j 0)) (ModuleCat.of k k) q
        rw [(serreSpectralSequenceFirstPageXIsoSigma (univ : Set B) hp k d q (serreBideg d q)
            (by simp [serreBideg]) (by simp [serreBideg]; ring)).toLinearEquiv.finrank_eq,
          finrank_sigmaObj, ComplexShape.eulerCharSignsCohomologicalSpectralSequence_χ,
          show (serreBideg d q).1 + (serreBideg d q).2 = -((q + d : ℕ) : ℤ) by
            simp [serreBideg]; ring,
          coe_negOnePow_neg_natCast, pow_add, Nat.cast_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j : cell (univ : Set B) d, (-1 : ℤ) ^ d * eulerChar (p.fiber (map d j 0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.mul_sum, eulerChar_eq_finsum_finrank_singularHomology _ k,
          ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (hQ d (Finset.mem_range.1 hd) j)]

include hp in
/-- **Euler characteristic of the pages of the Serre spectral sequence.** Over a finite CW complex
`B` (`univ : Set B`) and a division ring `k`, if every fibre of `p : E ⟶ B` has finite CW type, then
every page `r ≥ 2` (in particular the `E¹` page `r = 2` and the `E²` page `r = 3`) has Euler
characteristic equal to the alternating cellwise sum of the Euler characteristics of the fibres over
the cell centres. -/
theorem eulerChar_serreSpectralSequence_page (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] (r : ℤ) (hr : 2 ≤ r) :
    ((serreSpectralSequence (univ : Set B) p k).page r).eulerChar =
      ∑ᶠ d : ℕ, (-1 : ℤ) ^ d *
        ∑ᶠ j : cell (univ : Set B) d, eulerChar (p.fiber (map d j 0)) := by
  obtain ⟨D, Q, hD, hQ⟩ := exists_cell_and_fiber_vanishing_bounds p k
  rw [CohomologicalSpectralSequence.eulerChar_page_eq_of_le
      (serreSpectralSequence (univ : Set B) p k) le_rfl
      (fun pq hpq ↦ isZero_serreSpectralSequence_page_two_X_of_notMem hp k hD hQ hpq)
      (fun pq _ ↦ finite_serreSpectralSequence_page_two_X hp k pq) r hr,
    eulerChar_serreSpectralSequence_page_two_eq_sum_range hp k hD hQ,
    finsum_eq_sum_of_support_subset _ (s := Finset.range D) (fun d hd ↦ by
      by_contra hge
      have := hD d (by simpa using hge)
      simp [finsum_of_isEmpty] at hd)]

include hp in
/-- Strong convergence over a finite CW base equates the Euler characteristic of page `2` of the
Serre spectral sequence with the alternating sum of the ranks of `serreSpectralObject`'s abutment.
-/
private lemma eulerChar_serreSpectralSequence_page_two_eq_sum_abutment (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] {D Q : ℕ}
    (hD : ∀ d ≥ D, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < D, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (map d j 0)))) :
    ((serreSpectralSequence (univ : Set B) p k).page 2).eulerChar =
      ∑ n ∈ Finset.range (D + Q), (-1 : ℤ) ^ n *
        finrank k ((serreSpectralObject (univ : Set B) p k).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p k
  set X_so := serreSpectralObject (univ : Set B) p k
  let S : Finset (ℤ × ℤ) := (Finset.range D ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2
  let N : ℕ := D + Q
  let I : Finset ℤ := (Finset.range N).image fun n : ℕ ↦ -(n : ℤ)
  let r : ℤ := (N : ℤ) + 3
  have hS_sub (pq : ℤ × ℤ) (hpq : pq ∈ S) :
      pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico (-1 : ℤ) (N : ℤ) := by
    rcases Finset.mem_image.1 hpq with ⟨⟨d, q⟩, hdq, rfl⟩
    rcases Finset.mem_product.1 hdq with ⟨hd, hq⟩
    have hd' := Finset.mem_range.1 hd
    have hq' := Finset.mem_range.1 hq
    refine ⟨Finset.mem_image.2 ⟨q + d, Finset.mem_range.2 (by lia), ?_⟩,
      Finset.mem_Ico.2 ⟨by simp [serreBideg]; lia, by simp [serreBideg]; lia⟩⟩
    simp [serreBideg]
    ring
  rw [← CohomologicalSpectralSequence.eulerChar_page_eq_of_le E_ss le_rfl
      (s := S) (fun pq hpq ↦ isZero_serreSpectralSequence_page_two_X_of_notMem hp k hD hQ hpq)
      (fun pq _ ↦ finite_serreSpectralSequence_page_two_X hp k pq) r (by lia),
    CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment E_ss X_so (by lia : (2 : ℤ) ≤ r) I
      (by lia : (-1 : ℤ) ≤ (N : ℤ))
      (fun m _ ↦ isZero_serreSpectralObject_abutmentFiltration p k univ (by lia) m)
      (fun m hm ↦ by
        rcases Finset.mem_image.1 hm with ⟨n, hn, rfl⟩
        exact isIso_serreSpectralObject_abutmentFiltrationι hp k univ (subset_univ _) n
          (by have := Finset.mem_range.1 hn; lia))
      (fun pq hpq ↦ E_ss.isZero_page_X_of_le le_rfl
        (isZero_serreSpectralSequence_page_two_X_of_notMem hp k hD hQ
          fun hmem ↦ hpq (hS_sub pq hmem)) r (by lia))
      (fun pq _ _ ↦ E_ss.finite_page_X_of_le le_rfl
        (finite_serreSpectralSequence_page_two_X hp k pq) r (by lia))
      (fun pq hI hIco ↦ by
        rcases Finset.mem_image.1 hI with ⟨n, hn, hsum⟩
        have hn' := Finset.mem_range.1 hn
        have hb' := Finset.mem_Ico.1 hIco
        exact ⟨serreSpectralSequencePageXIsoGraded hp k (subset_univ _) r (by lia) pq
          (by lia) (by lia)⟩),
    Finset.sum_image (fun n₁ _ n₂ _ h ↦ by lia)]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [coe_negOnePow_neg_natCast]

include hp in
/-- Over a finite CW base `B` and a Noetherian ring `R`, the abutment of `serreSpectralObject` is
finitely generated in every degree `-n`. -/
private lemma finite_serreSpectralObject_abutment (R : Type u) [Ring R] [IsNoetherianRing R]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] (n : ℕ) :
    Module.Finite R ((serreSpectralObject (univ : Set B) p R).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p R
  set X_so := serreSpectralObject (univ : Set B) p R
  let r : ℤ := (n : ℤ) + 4
  refine X_so.finite_abutment_of_forall_finite_cokernel (by lia : (-1 : ℤ) ≤ (n : ℤ))
    (isZero_serreSpectralObject_abutmentFiltration p R univ (by lia) _)
    (isIso_serreSpectralObject_abutmentFiltrationι hp R univ (subset_univ _) n le_rfl)
    fun q hq ↦ ?_
  have hq' := Finset.mem_Ico.1 hq
  have : Module.Finite R ((E_ss.page r (by lia)).X (-(n : ℤ) - q, q)) :=
    E_ss.finite_page_X_of_le le_rfl
      (finite_serreSpectralSequence_page_two_X hp R (-(n : ℤ) - q, q)) r (by lia)
  have iso := serreSpectralSequencePageXIsoGraded hp R (subset_univ _) r (by lia)
    (-(n : ℤ) - q, q) (by lia) (by lia)
  dsimp only at iso
  rw [sub_add_cancel] at iso
  exact .equiv iso.toLinearEquiv

include hp in
/-- Given cell and fibre vanishing bounds `(D, Q)` on `B`, the abutment of `serreSpectralObject`
vanishes in degree `-n` for all `n ≥ D + Q`. -/
private lemma isZero_serreSpectralObject_abutment_of_bounds (R : Type u) [Ring R] {D Q : ℕ}
    (hD : ∀ d ≥ D, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < D, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d j 0))))
    {n : ℕ} (hn : D + Q ≤ n) :
    IsZero ((serreSpectralObject (univ : Set B) p R).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p R
  set X_so := serreSpectralObject (univ : Set B) p R
  let r : ℤ := (n : ℤ) + 4
  refine X_so.isZero_abutment_of_forall_isZero_cokernel (by lia : (-1 : ℤ) ≤ (n : ℤ))
    (isZero_serreSpectralObject_abutmentFiltration p R univ (by lia) _)
    (isIso_serreSpectralObject_abutmentFiltrationι hp R univ (subset_univ _) n le_rfl)
    fun b hb ↦ ?_
  have hb' := Finset.mem_Ico.1 hb
  have hnotMem : (-(n : ℤ) - b, b) ∉
      (Finset.range D ×ˢ Finset.range Q).image (fun dq ↦ serreBideg dq.1 dq.2) := by
    intro hmem
    rcases Finset.mem_image.1 hmem with ⟨⟨d, q⟩, hdq, h⟩
    rcases Finset.mem_product.1 hdq with ⟨hd, hq⟩
    have := Finset.mem_range.1 hd
    have := Finset.mem_range.1 hq
    simp only [serreBideg, Prod.mk.injEq] at h
    lia
  have hzero_r : IsZero ((E_ss.page r (by lia)).X (-(n : ℤ) - b, b)) :=
    E_ss.isZero_page_X_of_le le_rfl
      (isZero_serreSpectralSequence_page_two_X_of_notMem hp R hD hQ hnotMem) r (by lia)
  have iso := serreSpectralSequencePageXIsoGraded hp R (subset_univ _) r (by lia)
    (-(n : ℤ) - b, b) (by lia) (by lia)
  dsimp only at iso
  rw [sub_add_cancel] at iso
  exact hzero_r.of_iso iso.symm

end CWBase

/-! ### Serre fibrations over a base of finite CW type -/

section SerreFibration

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)

include hp in
/-- **Finiteness of singular homology for the total space of a Serre fibration.** Over a Noetherian
ring `R`, if `p : E ⟶ B` is a Serre fibration whose base `B` and fibres `p⁻¹(b)` all have finite CW
type, then `H_n(E; R)` is finitely generated in every degree `n`. -/
theorem finite_singularHomology_of_mem_serreFibrations (R : Type u) [Ring R] [IsNoetherianRing R]
    [FiniteCWType B] [∀ b, FiniteCWType (p.fiber b)] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨B', _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of B' ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  have (b' : _root_.TopCat.of B') : FiniteCWType ((_root_.TopCat.pullbackFst g p).fiber b') :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g b')).finiteCWType
  have := finite_serreSpectralObject_abutment (mem_serreFibrations_pullbackFst hp g) R n
  exact .equiv (serreSpectralObjectPullbackAbutmentIso hp R (univ : Set B') (g := g)
    e.symm.isWeakHomotopyEquivalence n).toLinearEquiv

include hp in
/-- **Eventual vanishing of singular homology for the total space of a Serre fibration.** Over any
ring `R`, if `p : E ⟶ B` is a Serre fibration whose base `B` and fibres `p⁻¹(b)` all have finite CW
type, then `H_n(E; R)` vanishes for all sufficiently large `n`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations (R : Type u) [Ring R]
    [FiniteCWType B] [∀ b, FiniteCWType (p.fiber b)] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨B', _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of B' ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  have (b' : _root_.TopCat.of B') : FiniteCWType ((_root_.TopCat.pullbackFst g p).fiber b') :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g b')).finiteCWType
  obtain ⟨D, Q, hD, hQ⟩ := exists_cell_and_fiber_vanishing_bounds (_root_.TopCat.pullbackFst g p) R
  refine Filter.eventually_atTop.2 ⟨D + Q, fun n hn ↦ ?_⟩
  exact (isZero_serreSpectralObject_abutment_of_bounds (mem_serreFibrations_pullbackFst hp g) R
    hD hQ hn).of_iso
    (serreSpectralObjectPullbackAbutmentIso hp R (univ : Set B') (g := g)
      e.symm.isWeakHomotopyEquivalence n).symm

include hp in
/-- **Multiplicativity of the Euler characteristic for a Serre fibration with constant fibre Euler
characteristic.** Over any division ring `k`, if `p : E ⟶ B` is a Serre fibration whose base `B` and
fibres `p⁻¹(b)` have finite CW type and every fibre has Euler characteristic `c`, then
`∑ᶠ i, (-1)^i dim_k H_i(E; k) = χ(B) · c`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations (k : Type u) [DivisionRing k]
    [FiniteCWType B] [∀ b, FiniteCWType (p.fiber b)] {c : ℤ}
    (hc : ∀ b, eulerChar (p.fiber b) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) =
      eulerChar B * c := by
  obtain ⟨B', _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  let g : _root_.TopCat.of B' ⟶ B := _root_.TopCat.ofHom e.symm.toFun
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  have (b' : _root_.TopCat.of B') : FiniteCWType (p'.fiber b') :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g b')).finiteCWType
  obtain ⟨D, Q, hD, hQ⟩ := exists_cell_and_fiber_vanishing_bounds p' k
  have hvan (n : ℕ) (hn : D + Q ≤ n) :
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) :=
    (isZero_serreSpectralObject_abutment_of_bounds hp' k hD hQ hn).of_iso
      (serreSpectralObjectPullbackAbutmentIso hp k (univ : Set B') (g := g)
        e.symm.isWeakHomotopyEquivalence n).symm
  -- Compare the total-space Betti sum and the CW base sum through page `2` of the pullback
  -- spectral sequence.
  have habut : ∑ n ∈ Finset.range (D + Q), (-1 : ℤ) ^ n * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      ((serreSpectralSequence (univ : Set B') p' k).page 2).eulerChar := by
    rw [eulerChar_serreSpectralSequence_page_two_eq_sum_abutment hp' k hD hQ]
    exact Finset.sum_congr rfl fun n _ ↦ by
      rw [(serreSpectralObjectPullbackAbutmentIso hp k (univ : Set B') (g := g)
        e.symm.isWeakHomotopyEquivalence n).toLinearEquiv.finrank_eq]
  rw [ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range hvan, habut,
    eulerChar_serreSpectralSequence_page_two_eq_sum_range hp' k hD hQ,
    eulerChar_eq_cwEulerChar (e.trans (Homeomorph.Set.univ B').symm.toHomotopyEquiv),
    cwEulerChar_eq_sum_range (univ : Set B') hD, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have : _root_.Finite (cell (univ : Set B') d) := FiniteType.finite_cell d
  let _ := Fintype.ofFinite (cell (univ : Set B') d)
  have hfib (j : cell (univ : Set B') d) : eulerChar (p'.fiber (map d j 0)) = c :=
    (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso g (map d j 0))).eulerChar_eq.trans (hc _)
  simp only [hfib, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  ring

include hp in
/-- If `p : E ⟶ B` is a Serre fibration between spaces of finite CW type whose fibres have finite CW
type and constant Euler characteristic `c`, then `χ(E) = χ(B) · c`. -/
theorem eulerChar_eq_mul_of_mem_serreFibrations [FiniteCWType E] [FiniteCWType B]
    [∀ b, FiniteCWType (p.fiber b)] {c : ℤ} (hc : ∀ b, eulerChar (p.fiber b) = c) :
    eulerChar E = eulerChar B * c := by
  rw [eulerChar_eq_finsum_finrank_singularHomology E (ULift.{u} ℚ)]
  exact finsum_finrank_singularHomology_of_mem_serreFibrations hp (ULift.{u} ℚ) hc

end SerreFibration

end TopCat

/-! ### Fibre bundles -/

section FiberBundle

/-- Each fibre of the projection of a fibre bundle `FiberBundle F E` is homeomorphic to the model
fibre `F`. -/
private def projFiberHomeomorph {B F : Type u} [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type u) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) :
    ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) ≃ₜ F :=
  (trivializationAt F E b).preimageSingletonHomeomorph (FiberBundle.mem_baseSet_trivializationAt' b)

/-- Over a Noetherian ring `R`, the singular homology of the total space of a fibre bundle whose
base and fibre have finite CW type is finitely generated in every degree. -/
theorem finite_singularHomology_fiberBundle (R : Type u) [Ring R] [IsNoetherianRing R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] (n : ℕ) :
    Module.Finite R (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).obj (TopCat.of (TotalSpace F E))) := by
  have (b : TopCat.of B) :
      FiniteCWType ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
        _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :=
    (projFiberHomeomorph E b).finiteCWType
  exact TopCat.finite_singularHomology_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_proj F E) R n

/-- Over any ring `R`, the singular homology of the total space of a fibre bundle whose base and
fibre have finite CW type vanishes in all sufficiently large degrees. -/
theorem eventually_isZero_singularHomology_fiberBundle (R : Type u) [Ring R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (TopCat.of (TotalSpace F E))) := by
  have (b : TopCat.of B) :
      FiniteCWType ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
        _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :=
    (projFiberHomeomorph E b).finiteCWType
  exact TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_proj F E) R

/-- **Multiplicativity of the Euler characteristic in fibre bundles.** For a fibre bundle `E` over
`B` with model fibre `F`, where `B` and `F` have finite CW type, and any division ring `k`, the
alternating sum of the dimensions of `H_i(TotalSpace F E; k)` equals `χ(B) · χ(F)`. No hypothesis on
monodromy and no finite CW model of the total space are assumed. -/
theorem finsum_finrank_singularHomology_fiberBundle (k : Type u) [DivisionRing k]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj
        (ModuleCat.of k k)).obj (TopCat.of (TotalSpace F E))) : ℤ) =
      eulerChar B * eulerChar F := by
  have (b : TopCat.of B) :
      FiniteCWType ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
        _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :=
    (projFiberHomeomorph E b).finiteCWType
  exact TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_proj F E) k fun b ↦ (projFiberHomeomorph E b).eulerChar_eq

/-- **Multiplicativity of `eulerChar` for fibre bundles.** When `B`, `F`, and `TotalSpace F E` all
have finite CW type, `χ(TotalSpace F E) = χ(B) · χ(F)`. -/
theorem eulerChar_totalSpace_fiberBundle
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] [FiniteCWType (TotalSpace F E)] :
    eulerChar (TotalSpace F E) = eulerChar B * eulerChar F := by
  rw [eulerChar_eq_finsum_finrank_singularHomology (TotalSpace F E) (ULift.{u} ℚ)]
  exact finsum_finrank_singularHomology_fiberBundle (ULift.{u} ℚ) E

end FiberBundle

end TauCeti

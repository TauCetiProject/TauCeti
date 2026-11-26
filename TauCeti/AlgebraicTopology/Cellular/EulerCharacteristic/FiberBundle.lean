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
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
public import TauCeti.Topology.Category.TopCat.Fiber
import TauCeti.Algebra.Category.ModuleCat.Colimits
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Algebra.Homology.SpectralObject.Finrank
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
import TauCeti.Algebra.Homology.SpectralSequence.EulerCharacteristic
import TauCeti.Algebra.Homology.SpectralSequence.ModuleCat
import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase
import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
import TauCeti.Topology.CWComplex.Comparison
import TauCeti.Topology.FiberBundle.TopCat
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

* `TauCeti.TopCat.eulerChar_serreSpectralSequence_page`: over a finite relative CW complex
  `(C, D)` in `B`, every page `r ≥ 2` of the Serre spectral sequence of `p` over a division ring
  `k` has Euler characteristic `∑ᶠ d, (-1)^d ∑ᶠ j : cell C d, χ(p⁻¹(χ_j(0)))`.
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
* J. R. Klein, C. Malkiewich, M. Ramzi, *On the multiplicativity of the Euler characteristic*,
  arXiv:2211.04992v2 (2023), Introduction, pp. 1–2.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 1.15 and Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (§1.1, Theorem 1.3 and the local-coefficient version).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Bundle Topology Topology.RelCWComplex AlgebraicTopology

universe u

namespace TauCeti

/-! ### Spectral sequence bidegree helpers -/

/-- Bidegree `(1 - q - 2d, d - 1)` on page `2` of `serreSpectralSequence` corresponding to base
cell dimension `d` and fibre homology degree `q`. -/
private def serreBideg (d q : ℕ) : ℤ × ℤ :=
  (1 - (q : ℤ) - 2 * (d : ℤ), (d : ℤ) - 1)

@[simp]
private lemma serreBideg_fst (d q : ℕ) : (serreBideg d q).1 = 1 - (q : ℤ) - 2 * (d : ℤ) := rfl

@[simp]
private lemma serreBideg_snd (d q : ℕ) : (serreBideg d q).2 = (d : ℤ) - 1 := rfl

private lemma serreBideg_add (d q : ℕ) :
    (serreBideg d q).1 + (serreBideg d q).2 = -((q + d : ℕ) : ℤ) := by
  simp only [serreBideg_fst, serreBideg_snd, Nat.cast_add]
  ring

private lemma serreBideg_injective : Function.Injective2 serreBideg := by
  intro d₁ q₁ d₂ q₂ h
  simp only [serreBideg, Prod.mk.injEq] at h
  lia

namespace TopCat

/-! ### Serre spectral sequence over a finite relative CW base -/

section RelCWBase

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  [T2Space B] {C D : Set B} [RelCWComplex C D]

omit [T2Space B] in
/-- Uniform dimension bound `M` on the cells of `C` together with a uniform degree bound `Q` above
which the homology of every cell-centre fibre `p⁻¹(χ_j(0))` vanishes. -/
private lemma exists_cell_and_fiber_vanishing_bounds (C : Set B) {D : Set B} [RelCWComplex C D]
    (p : E ⟶ B) (R : Type u) [Ring R] [RelCWComplex.Finite C] [∀ b, FiniteCWType (p.fiber b)] :
    ∃ M Q : ℕ, (∀ d ≥ M, IsEmpty (cell C d)) ∧
      ∀ d < M, ∀ (j : cell C d), ∀ q ≥ Q,
        IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
          (p.fiber (map d j 0))) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  have hbound : ∀ (d : Fin M) (j : cell C d.val), ∃ Q : ℕ, ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d.val j 0))) := fun d j ↦
    Filter.eventually_atTop.1
      (eventually_isZero_singularHomology_of_finiteCWType (p.fiber (map d.val j 0))
        (ModuleCat.of R R))
  choose Qfn hQfn using hbound
  have : ∀ d : Fin M, _root_.Finite (cell C d.val) := fun d ↦ FiniteType.finite_cell d.val
  let _ := Fintype.ofFinite (Σ d : Fin M, cell C d.val)
  refine ⟨M, Finset.univ.sup (fun dj : Σ d : Fin M, cell C d.val ↦ Qfn dj.1 dj.2),
    hM, fun d hd j q hq ↦ hQfn ⟨d, hd⟩ j q ?_⟩
  exact (Finset.le_sup (f := fun dj : Σ d : Fin M, cell C d.val ↦ Qfn dj.1 dj.2)
    (Finset.mem_univ ⟨⟨d, hd⟩, j⟩)).trans hq

include hp in
variable (C) in
/-- Given cell and fibre vanishing bounds `(M, Q)` on `C`, page `2` of the Serre spectral sequence
of `p : E ⟶ B` vanishes outside `image serreBideg (range M ×ˢ range Q)`. -/
private lemma isZero_serreSpectralSequence_page_two_X_of_notMem (R : Type u) [Ring R] {M Q : ℕ}
    (hM : ∀ d ≥ M, IsEmpty (cell C d))
    (hQ : ∀ d < M, ∀ (j : cell C d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d j 0))))
    {pq : ℤ × ℤ}
    (hpq : pq ∉ (Finset.range M ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2) :
    IsZero (((serreSpectralSequence C p R).page 2).X pq) := by
  by_cases hb : pq.2 < -1
  · exact isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two R C pq (by lia)
  · by_cases hq : 0 ≤ pq.1 + 2 * pq.2
    · exact isZero_serreSpectralSequence_page_two_X hp R C pq hq
    · set d := (pq.2 + 1).toNat
      set q := (-pq.1 - 2 * pq.2 - 1).toNat
      have hpq_eq : pq = serreBideg d q := by
        ext <;> simp only [serreBideg_fst, serreBideg_snd] <;> lia
      refine ((colimit.isColimit _).isZero_pt (Functor.isZero _ fun ⟨j⟩ ↦ ?_)).of_iso
        (serreSpectralSequenceFirstPageXIsoSigma C hp R d q pq (by lia) (by lia))
      rcases lt_or_ge d M with hdM | hdM
      · refine hQ d hdM j q ?_
        by_contra hlt
        exact hpq (Finset.mem_image.2 ⟨(d, q),
          Finset.mem_product.2 ⟨Finset.mem_range.2 hdM, Finset.mem_range.2 (by lia)⟩,
          hpq_eq.symm⟩)
      · exact (hM d hdM).elim j

include hp in
variable (C) in
/-- Over a finite relative CW complex `(C, D)` and a Noetherian ring `R`, every term on page `2` of
the Serre spectral sequence of `p : E ⟶ B` is finitely generated once all fibres have finite CW
type. -/
private lemma finite_serreSpectralSequence_page_two_X (R : Type u) [Ring R] [IsNoetherianRing R]
    [RelCWComplex.Finite C] [∀ b, FiniteCWType (p.fiber b)] (pq : ℤ × ℤ) :
    Module.Finite R (((serreSpectralSequence C p R).page 2).X pq) := by
  by_cases hb : pq.2 < -1
  · have := _root_.ModuleCat.subsingleton_of_isZero
      (isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two (p := p) R C pq (by lia))
    infer_instance
  · by_cases hq : 0 ≤ pq.1 + 2 * pq.2
    · have := _root_.ModuleCat.subsingleton_of_isZero
        (isZero_serreSpectralSequence_page_two_X hp R C pq hq)
      infer_instance
    · set d := (pq.2 + 1).toNat
      set q := (-pq.1 - 2 * pq.2 - 1).toNat
      have : _root_.Finite (cell C d) := FiniteType.finite_cell d
      have (j : cell C d) :
          Module.Finite R (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (map d j 0))) :=
        finite_singularHomology_of_finiteCWType (p.fiber (map d j 0)) (ModuleCat.of R R) q
      have : Module.Finite R ↥(∐ fun j : cell C d ↦
          ((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
            (p.fiber (map d j 0))) :=
        TauCeti.ModuleCat.finite_coproduct_of_finite_support _ (Set.toFinite _)
      exact .equiv (serreSpectralSequenceFirstPageXIsoSigma C hp R d q pq
        (by lia) (by lia)).symm.toLinearEquiv

include hp in
variable (C) in
/-- Over a finite relative CW complex `(C, D)` and a division ring `k`, the Euler characteristic of
page `2` of the Serre spectral sequence is the alternating sum over `range M` of the cell-centre
fibre Euler characteristics. -/
private lemma eulerChar_serreSpectralSequence_page_two_eq_sum_range (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite C] [∀ b, FiniteCWType (p.fiber b)] {M Q : ℕ}
    (hM : ∀ d ≥ M, IsEmpty (cell C d))
    (hQ : ∀ d < M, ∀ (j : cell C d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (map d j 0)))) :
    ((serreSpectralSequence C p k).page 2).eulerChar =
      ∑ d ∈ Finset.range M, (-1 : ℤ) ^ d *
        ∑ᶠ j : cell C d, eulerChar (p.fiber (map d j 0)) := by
  let S : Finset (ℤ × ℤ) := (Finset.range M ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2
  rw [((serreSpectralSequence C p k).page 2).eulerChar_eq_sum_of_forall_notMem (s := S)
      (fun _ hpq ↦ isZero_serreSpectralSequence_page_two_X_of_notMem hp C k hM hQ hpq),
    Finset.sum_image (fun dq₁ _ dq₂ _ h ↦ Prod.ext
      (serreBideg_injective h).1 (serreBideg_injective h).2), Finset.sum_product]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have : _root_.Finite (cell C d) := FiniteType.finite_cell d
  let _ := Fintype.ofFinite (cell C d)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  calc
    ∑ q ∈ Finset.range Q,
        (((ComplexShape.up' (⟨2, 1 - 2⟩ : ℤ × ℤ)).χ (serreBideg d q) : ℤ) *
          finrank k (((serreSpectralSequence C p k).page 2).X (serreBideg d q)))
      = ∑ q ∈ Finset.range Q, ∑ j : cell C d,
          (-1 : ℤ) ^ d * ((-1 : ℤ) ^ q * finrank k
            (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
              (p.fiber (map d j 0)))) := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        have (j : cell C d) :
            Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) q).obj
              (ModuleCat.of k k)).obj (p.fiber (map d j 0))) :=
          finite_singularHomology_of_finiteCWType (p.fiber (map d j 0)) (ModuleCat.of k k) q
        rw [(serreSpectralSequenceFirstPageXIsoSigma C hp k d q (serreBideg d q)
            (by simp) (serreBideg_add d q)).toLinearEquiv.finrank_eq,
          _root_.ModuleCat.finrank_sigmaObj]
        simp only [ComplexShape.eulerCharSignsCohomologicalSpectralSequence_χ, serreBideg_add,
          Int.negOnePow_neg, Int.coe_negOnePow_natCast, pow_add, Nat.cast_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j : cell C d, (-1 : ℤ) ^ d * eulerChar (p.fiber (map d j 0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.mul_sum, eulerChar_eq_finsum_finrank_singularHomology _ k,
          _root_.ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range
            (hQ d (Finset.mem_range.1 hd) j)]

include hp in
variable (C) in
/-- **Euler characteristic of the pages of the Serre spectral sequence.** Over a finite relative CW
complex `(C, D)` in `B` and a division ring `k`, if every fibre of `p : E ⟶ B` has finite CW type,
then every page `r ≥ 2` (in particular the `E¹` page `r = 2` and the `E²` page `r = 3`) has Euler
characteristic equal to the alternating cellwise sum of the Euler characteristics of the fibres over
the cell centres of `C`. -/
theorem eulerChar_serreSpectralSequence_page (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite C] [∀ b, FiniteCWType (p.fiber b)] (r : ℤ) (hr : 2 ≤ r) :
    ((serreSpectralSequence C p k).page r).eulerChar =
      ∑ᶠ d : ℕ, (-1 : ℤ) ^ d *
        ∑ᶠ j : cell C d, eulerChar (p.fiber (map d j 0)) := by
  obtain ⟨M, Q, hM, hQ⟩ := exists_cell_and_fiber_vanishing_bounds C p k
  rw [CohomologicalSpectralSequence.eulerChar_page_eq_of_le
      (serreSpectralSequence C p k) le_rfl
      (fun _ hpq ↦ isZero_serreSpectralSequence_page_two_X_of_notMem hp C k hM hQ hpq)
      (fun pq _ ↦ finite_serreSpectralSequence_page_two_X hp C k pq) r hr,
    eulerChar_serreSpectralSequence_page_two_eq_sum_range hp C k hM hQ,
    finsum_eq_sum_of_support_subset _ (s := Finset.range M) (fun d hd ↦ by
      by_contra hge
      have := hM d (by simpa using hge)
      simp [finsum_of_isEmpty] at hd)]

end RelCWBase

section CWBase

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  [T2Space B] [CWComplex (univ : Set B)]

include hp in
/-- Strong convergence of `serreSpectralSequence` at `(m - b, b)` in total degree `m`. -/
private def serrePageXIsoGraded (R : Type u) [Ring R] (r m b : ℤ) (hr : 2 ≤ r)
    (hra : b + 3 ≤ r) (hrb : 2 - m - b ≤ r) :
    ((serreSpectralSequence (univ : Set B) p R).page r).X (m - b, b) ≅
      cokernel ((serreSpectralObject (univ : Set B) p R).abutmentFiltrationMap b m) :=
  serreSpectralSequencePageXIsoGraded hp R (subset_univ _) r hr (m - b, b) hra (by lia) ≪≫
    eqToIso (congrArg (fun t ↦ cokernel
      ((serreSpectralObject (univ : Set B) p R).abutmentFiltrationMap b t))
      (sub_add_cancel m b))

include hp in
/-- Strong convergence over a finite CW base equates the Euler characteristic of page `2` of the
Serre spectral sequence with the alternating sum of the ranks of `serreSpectralObject`'s abutment.
-/
private lemma eulerChar_serreSpectralSequence_page_two_eq_sum_abutment (k : Type u) [DivisionRing k]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] {M Q : ℕ}
    (hM : ∀ d ≥ M, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < M, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber (map d j 0)))) :
    ((serreSpectralSequence (univ : Set B) p k).page 2).eulerChar =
      ∑ n ∈ Finset.range (M + Q), (-1 : ℤ) ^ n *
        finrank k ((serreSpectralObject (univ : Set B) p k).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p k
  set X_so := serreSpectralObject (univ : Set B) p k
  let S : Finset (ℤ × ℤ) := (Finset.range M ×ˢ Finset.range Q).image fun dq ↦ serreBideg dq.1 dq.2
  let N : ℕ := M + Q
  let I : Finset ℤ := (Finset.range N).image fun n : ℕ ↦ -(n : ℤ)
  let r : ℤ := (N : ℤ) + 3
  have hS_sub (pq : ℤ × ℤ) (hpq : pq ∈ S) :
      pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico (-1 : ℤ) (N : ℤ) := by
    rcases Finset.mem_image.1 hpq with ⟨⟨d, q⟩, hdq, rfl⟩
    rcases Finset.mem_product.1 hdq with ⟨hd, hq⟩
    have hd' := Finset.mem_range.1 hd
    have hq' := Finset.mem_range.1 hq
    exact ⟨Finset.mem_image.2 ⟨q + d, Finset.mem_range.2 (by lia), (serreBideg_add d q).symm⟩,
      Finset.mem_Ico.2 ⟨by simp only [serreBideg_snd]; lia, by simp only [serreBideg_snd]; lia⟩⟩
  rw [← CohomologicalSpectralSequence.eulerChar_page_eq_of_le E_ss le_rfl
      (s := S) (fun _ hpq ↦ isZero_serreSpectralSequence_page_two_X_of_notMem hp univ k hM hQ hpq)
      (fun pq _ ↦ finite_serreSpectralSequence_page_two_X hp univ k pq) r (by lia),
    CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment E_ss X_so (by lia : (2 : ℤ) ≤ r) I
      (by lia : (-1 : ℤ) ≤ (N : ℤ))
      (fun m _ ↦ isZero_serreSpectralObject_abutmentFiltration p k univ (by lia) m)
      (fun m hm ↦ by
        rcases Finset.mem_image.1 hm with ⟨n, hn, rfl⟩
        exact isIso_serreSpectralObject_abutmentFiltrationι hp k univ (subset_univ _) n
          (by have := Finset.mem_range.1 hn; lia))
      (fun pq hpq ↦ E_ss.isZero_page_X_of_le le_rfl
        (isZero_serreSpectralSequence_page_two_X_of_notMem hp univ k hM hQ
          fun hmem ↦ hpq (hS_sub pq hmem)) r (by lia))
      (fun m _ b _ ↦ E_ss.finite_page_X_of_le le_rfl
        (finite_serreSpectralSequence_page_two_X hp univ k (m - b, b)) r (by lia))
      (fun m hI b hIco ↦ by
        rcases Finset.mem_image.1 hI with ⟨n, hn, rfl⟩
        have := Finset.mem_range.1 hn
        have := Finset.mem_Ico.1 hIco
        exact ⟨serrePageXIsoGraded hp k r (-(n : ℤ)) b (by lia) (by lia) (by lia)⟩),
    Finset.sum_image (fun n₁ _ n₂ _ h ↦ by lia)]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [Int.negOnePow_neg, Int.coe_negOnePow_natCast]

include hp in
/-- Over a finite CW base `B` and a Noetherian ring `R`, the abutment of `serreSpectralObject` is
finitely generated in every degree `-n`. -/
private lemma finite_serreSpectralObject_abutment (R : Type u) [Ring R] [IsNoetherianRing R]
    [RelCWComplex.Finite (univ : Set B)] [∀ b, FiniteCWType (p.fiber b)] (n : ℕ) :
    Module.Finite R ((serreSpectralObject (univ : Set B) p R).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p R
  set X_so := serreSpectralObject (univ : Set B) p R
  let r : ℤ := (n : ℤ) + 4
  have hfin_a : Module.Finite R (X_so.abutmentFiltration (-1) (-(n : ℤ))) := by
    have := _root_.ModuleCat.subsingleton_of_isZero
      (isZero_serreSpectralObject_abutmentFiltration p R univ (b := -1) (by lia) (-(n : ℤ)))
    infer_instance
  refine X_so.finite_abutment_of_forall_finite_cokernel (by lia : (-1 : ℤ) ≤ (n : ℤ)) hfin_a
    (isIso_serreSpectralObject_abutmentFiltrationι hp R univ (subset_univ _) n le_rfl)
    fun q hq ↦ ?_
  have := Finset.mem_Ico.1 hq
  have : Module.Finite R ((E_ss.page r (by lia)).X (-(n : ℤ) - q, q)) :=
    E_ss.finite_page_X_of_le le_rfl
      (finite_serreSpectralSequence_page_two_X hp univ R (-(n : ℤ) - q, q)) r (by lia)
  exact .equiv
    (serrePageXIsoGraded hp R r (-(n : ℤ)) q (by lia) (by lia) (by lia)).toLinearEquiv

include hp in
/-- Given cell and fibre vanishing bounds `(M, Q)` on `B`, the abutment of `serreSpectralObject`
vanishes in degree `-n` for all `n ≥ M + Q`. -/
private lemma isZero_serreSpectralObject_abutment_of_bounds (R : Type u) [Ring R] {M Q : ℕ}
    (hM : ∀ d ≥ M, IsEmpty (cell (univ : Set B) d))
    (hQ : ∀ d < M, ∀ (j : cell (univ : Set B) d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        (p.fiber (map d j 0))))
    {n : ℕ} (hn : M + Q ≤ n) :
    IsZero ((serreSpectralObject (univ : Set B) p R).abutment (-(n : ℤ))) := by
  set E_ss := serreSpectralSequence (univ : Set B) p R
  set X_so := serreSpectralObject (univ : Set B) p R
  let r : ℤ := (n : ℤ) + 4
  refine X_so.isZero_abutment_of_forall_isZero_cokernel (by lia : (-1 : ℤ) ≤ (n : ℤ))
    (isZero_serreSpectralObject_abutmentFiltration p R univ (by lia) _)
    (isIso_serreSpectralObject_abutmentFiltrationι hp R univ (subset_univ _) n le_rfl)
    fun b hb ↦ ?_
  have := Finset.mem_Ico.1 hb
  have hnotMem : (-(n : ℤ) - b, b) ∉
      (Finset.range M ×ˢ Finset.range Q).image (fun dq ↦ serreBideg dq.1 dq.2) := by
    intro hmem
    rcases Finset.mem_image.1 hmem with ⟨⟨d, q⟩, hdq, h⟩
    rcases Finset.mem_product.1 hdq with ⟨hd, hq⟩
    have := Finset.mem_range.1 hd
    have := Finset.mem_range.1 hq
    simp only [serreBideg, Prod.mk.injEq] at h
    lia
  have hzero_r : IsZero ((E_ss.page r (by lia)).X (-(n : ℤ) - b, b)) :=
    E_ss.isZero_page_X_of_le le_rfl
      (isZero_serreSpectralSequence_page_two_X_of_notMem hp univ R hM hQ hnotMem) r (by lia)
  exact hzero_r.of_iso
    (serrePageXIsoGraded hp R r (-(n : ℤ)) b (by lia) (by lia) (by lia)).symm

end CWBase

/-! ### Serre fibrations over a base of finite CW type -/

section SerreFibration

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)

/-- Pullback of `p : E ⟶ B` along `e.symm : B' → B` for a homotopy equivalence `e : B ≃ₕ B'`. -/
private def pullbackSymm {B' : Type u} [TopologicalSpace B'] (p : E ⟶ B)
    (e : ContinuousMap.HomotopyEquiv B B') :=
  _root_.TopCat.pullbackFst (_root_.TopCat.ofHom e.symm.toFun) p

private instance {B' : Type u} [TopologicalSpace B'] (p : E ⟶ B) [∀ b, FiniteCWType (p.fiber b)]
    (e : ContinuousMap.HomotopyEquiv B B') (b' : B') :
    FiniteCWType ((pullbackSymm p e).fiber b') :=
  (_root_.TopCat.homeoOfIso
    (p.fiberPullbackFstIso (_root_.TopCat.ofHom e.symm.toFun) b')).finiteCWType

private lemma eulerChar_fiber_pullbackSymm {B' : Type u} [TopologicalSpace B'] (p : E ⟶ B)
    [∀ b, FiniteCWType (p.fiber b)] (e : ContinuousMap.HomotopyEquiv B B') (b' : B') :
    eulerChar ((pullbackSymm p e).fiber b') = eulerChar (p.fiber (e.symm b')) :=
  (_root_.TopCat.homeoOfIso (p.fiberPullbackFstIso (_root_.TopCat.ofHom e.symm.toFun) b') :
    ((pullbackSymm p e).fiber b') ≃ₜ p.fiber (e.symm b')).eulerChar_eq

include hp in
private lemma mem_serreFibrations_pullbackSymm {B' : Type u} [TopologicalSpace B']
    (e : ContinuousMap.HomotopyEquiv B B') :
    serreFibrations (pullbackSymm p e) :=
  mem_serreFibrations_pullbackFst hp (_root_.TopCat.ofHom e.symm.toFun)

include hp in
/-- Identification of the abutment of `serreSpectralObject` for `pullbackSymm p e` with
`H_n(E; R)`. -/
private def pullbackHomotopyEquivAbutmentIso {B' : Type u} [TopologicalSpace B'] [T2Space B']
    [CWComplex (univ : Set B')] (e : ContinuousMap.HomotopyEquiv B B') (R : Type u) [Ring R]
    (n : ℕ) :
    (serreSpectralObject (univ : Set B') (pullbackSymm p e) R).abutment (-n) ≅
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  serreSpectralObjectPullbackAbutmentIso hp R (univ : Set B')
    (g := _root_.TopCat.ofHom e.symm.toFun) e.symm.isWeakHomotopyEquivalence n

include hp in
/-- Vanishing of `H_n(E; R)` above `D + Q` from cell and fibre vanishing bounds on a CW base `B'`
homotopy equivalent to `B`. -/
private lemma isZero_singularHomology_of_homotopyEquiv_bounds {B' : Type u} [TopologicalSpace B']
    [T2Space B'] [CWComplex (univ : Set B')] (e : ContinuousMap.HomotopyEquiv B B') (R : Type u)
    [Ring R] {D Q : ℕ}
    (hD : ∀ d ≥ D, IsEmpty (cell (univ : Set B') d))
    (hQ : ∀ d < D, ∀ (j : cell (univ : Set B') d), ∀ q ≥ Q,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj
        ((pullbackSymm p e).fiber (map d j 0))))
    {n : ℕ} (hn : D + Q ≤ n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) :=
  (isZero_serreSpectralObject_abutment_of_bounds
    (mem_serreFibrations_pullbackSymm hp e) R hD hQ hn).of_iso
    (pullbackHomotopyEquivAbutmentIso hp e R n).symm

include hp in
/-- **Finiteness of singular homology for the total space of a Serre fibration.** Over a Noetherian
ring `R`, if `p : E ⟶ B` is a Serre fibration whose base `B` and fibres `p⁻¹(b)` all have finite CW
type, then `H_n(E; R)` is finitely generated in every degree `n`. -/
theorem finite_singularHomology_of_mem_serreFibrations (R : Type u) [Ring R] [IsNoetherianRing R]
    [FiniteCWType B] [∀ b, FiniteCWType (p.fiber b)] (n : ℕ) :
    Module.Finite R
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨B', _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  have := finite_serreSpectralObject_abutment (mem_serreFibrations_pullbackSymm hp e) R n
  exact .equiv (pullbackHomotopyEquivAbutmentIso hp e R n).toLinearEquiv

include hp in
/-- **Eventual vanishing of singular homology for the total space of a Serre fibration.** Over any
ring `R`, if `p : E ⟶ B` is a Serre fibration whose base `B` and fibres `p⁻¹(b)` all have finite CW
type, then `H_n(E; R)` vanishes for all sufficiently large `n`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations (R : Type u) [Ring R]
    [FiniteCWType B] [∀ b, FiniteCWType (p.fiber b)] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj E) := by
  obtain ⟨B', _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  obtain ⟨M, Q, hM, hQ⟩ :=
    exists_cell_and_fiber_vanishing_bounds (univ : Set B') (pullbackSymm p e) R
  exact Filter.eventually_atTop.2
    ⟨M + Q, fun _ hn ↦ isZero_singularHomology_of_homotopyEquiv_bounds hp e R hM hQ hn⟩

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
  have hp' := mem_serreFibrations_pullbackSymm hp e
  obtain ⟨M, Q, hM, hQ⟩ :=
    exists_cell_and_fiber_vanishing_bounds (univ : Set B') (pullbackSymm p e) k
  -- Compare the total-space Betti sum and the CW base sum through page `2` of the pullback
  -- spectral sequence.
  have habut : ∑ n ∈ Finset.range (M + Q), (-1 : ℤ) ^ n * finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj E) =
      ((serreSpectralSequence (univ : Set B') (pullbackSymm p e) k).page 2).eulerChar := by
    rw [eulerChar_serreSpectralSequence_page_two_eq_sum_abutment hp' k hM hQ]
    exact Finset.sum_congr rfl fun n _ ↦ by
      rw [(pullbackHomotopyEquivAbutmentIso hp e k n).toLinearEquiv.finrank_eq]
  rw [_root_.ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range
      (fun _ hn ↦ isZero_singularHomology_of_homotopyEquiv_bounds hp e k hM hQ hn), habut,
    eulerChar_serreSpectralSequence_page_two_eq_sum_range hp' (univ : Set B') k hM hQ,
    eulerChar_eq_cwEulerChar (e.trans (Homeomorph.Set.univ B').symm.toHomotopyEquiv),
    cwEulerChar_eq_sum_range (univ : Set B') hM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have : _root_.Finite (cell (univ : Set B') d) := FiniteType.finite_cell d
  let _ := Fintype.ofFinite (cell (univ : Set B') d)
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun j _ ↦
      (eulerChar_fiber_pullbackSymm p e (map d j 0)).trans (hc _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
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

private instance {B F : Type u} [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type u) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [FiniteCWType F] (b : TopCat.of B) :
    FiniteCWType ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :=
  (FiberBundle.projFiberHomeomorph F E b).finiteCWType

/-- Over a Noetherian ring `R`, the singular homology of the total space of a fibre bundle whose
base and fibre have finite CW type is finitely generated in every degree. -/
theorem finite_singularHomology_fiberBundle (R : Type u) [Ring R] [IsNoetherianRing R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] (n : ℕ) :
    Module.Finite R (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).obj (TopCat.of (TotalSpace F E))) :=
  TopCat.finite_singularHomology_of_mem_serreFibrations (TopCat.mem_serreFibrations_proj F E) R n

/-- Over any ring `R`, the singular homology of the total space of a fibre bundle whose base and
fibre have finite CW type vanishes in all sufficiently large degrees. -/
theorem eventually_isZero_singularHomology_fiberBundle (R : Type u) [Ring R]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∀ᶠ n in Filter.atTop,
      IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (TopCat.of (TotalSpace F E))) :=
  TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations
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
      eulerChar B * eulerChar F :=
  TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_proj F E) k fun b ↦
      (FiberBundle.projFiberHomeomorph F E b).eulerChar_eq

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

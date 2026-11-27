/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Comparison
public import TauCeti.Geometry.Symplectic.Floer.Cap.Ring

/-!
# The PSS maps of class-indexed counts are algebra isomorphisms

Fix two capped complexes as in `TauCeti.Geometry.Symplectic.Floer.Cap.Ring`, both graded by the
cochain degree `n - grading` and with all counts recorded by generating series in a common class
group `G` mapping to the period group by an area-preserving homomorphism `q`:

* the **Morse side**: finitely many critical points of a Morse function with capped generators
  `T` and reference generators `rM`, with the counts `DM` of rigid Morse trajectories as
  differential, the counts `M` of the rigid three-pointed genus-zero configurations with Morse
  incidence conditions as product (the Morse quantum product `⋆_M`), and a fundamental cycle `Z`;
* the **Floer side**: finitely many orbits of a Hamiltonian with capped generators `P` and
  reference caps `r`, with the counts `D` of rigid Floer cylinders as differential, the counts
  `Q` of rigid pairs of pants as product (the pair-of-pants product `⋆`), and the counts `E` of
  rigid PSS planes constrained by the fundamental cycle.

Under the identities of `TauCeti.Floer.cohomologyGRingOfCounts` on each side, the degree-wise
cohomologies are algebras over the ground ring. The Morse identities (unit and associativity up to
homotopy) are the chain-level forms of the fundamental-class and associativity laws of the quantum
product, which this file assumes rather than proves.

The Piunikhin–Salamon–Schwarz (PSS) maps are counted by generating series `Φ`, of half-cylinders
from critical points to orbits, and `Ψ`, from orbits to critical points. The module PSS
isomorphism supplies the identities saying that `Φ` and `Ψ` are chain maps and that `Ψ ∘ Φ` and
`Φ ∘ Ψ` are homotopic to the identities. The comparison family, which attaches PSS planes to the
three ends of a pair of pants and deforms the Hamiltonian perturbation to zero, supplies through
its counts `K` the comparison identity

`∑ᵢ ∑ⱼ Φₛᵢ Φₜⱼ ∑ₖ Qᵢⱼₖ Ψₖₗ - Mₛₜₗ = ∑ₘ Kₛₜₘ DMₘₗ + ∑ₘ DMₛₘ Kₘₜₗ + (-1)^e ∑ₘ DMₜₘ Kₛₘₗ`

with `e` the cochain degree of the reference generator of `s`. Together with the module homotopy
`Φ ∘ Ψ ≃ 1` it makes `Φ a ⋆ Φ b - Φ (a ⋆_M b)` a coboundary for all Morse cocycles `a` and `b`,
by `novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries` in the
namespace `TauCeti.Floer`. Hence:

* `TauCeti.Floer.pssAlgEquivOfCounts`: the maps induced by `Φ` on cohomology form an isomorphism of
  algebras over the ground ring from the cohomology ring of the Morse counts to that of the Floer
  counts, sending the class of a cocycle `a` to the class of `Φ a`
  (`TauCeti.Floer.pssAlgEquivOfCounts_of_mk`), with inverse induced by `Ψ`
  (`TauCeti.Floer.pssAlgEquivOfCounts_symm_of_mk`). This is multiplicative PSS for class-indexed
  counts: neither product is defined by transporting the other. The construction follows
  `TauCeti.Floer.continuationAlgEquivOfCounts` in
  `TauCeti.Geometry.Symplectic.Floer.Cap.Continuation`: both are instances of the isomorphism
  `TauCeti.Floer.algEquivOfCounts` of homotopy-inverse multiplicative counts, with the
  series-level continuation homotopy used there replaced here by the comparison identity of
  `TauCeti.Geometry.Symplectic.Floer.Cap.Comparison`.
* `TauCeti.Floer.novikovMapOfMatrix_coordinates_symm_coefficientComparison_sub_mem_coboundaries`:
  the image `Φ z` of the Morse fundamental cycle `z` differs from the unit cycle `e` of the Floer
  counts by a coboundary. So the unit of the pair-of-pants product is the image under PSS of the
  fundamental class, and its class is the same for every Morse cocycle `Z` of cochain degree zero
  which is a left unit of the Morse product up to homotopy. No identity relating `Z` and `E` is
  assumed: a multiplicative map onto degree-zero cohomology preserves units
  (`LinearMap.sub_mem_coboundaries_of_surjective_cohomologyMap`).

Identifying the cohomology ring of the Morse counts with the quantum cohomology ring of the target,
through the Morse–singular comparison and Poincaré duality, is a separate step. The count
identities, index conditions and potential bounds are the hypotheses that the compactified moduli
spaces are to supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200,
  Theorem 5.1.
* G. Lu, *An explicit isomorphism between Floer homology and quantum homology*, Pacific J. Math.
  213 (2004), Theorem 1.1 and Remark 1.2.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1, on the Piunikhin–Salamon–Schwarz isomorphism.
-/

public section

noncomputable section

namespace TauCeti.Floer

open _root_.DirectSum NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A) [CommRing R]
  {κ ι : Type*} [Fintype κ] [Fintype ι] {T : κ → Type*} {P : ι → Type*}
  [∀ s, AddTorsor (PeriodGroup ω c) (T s)] [∀ i, AddTorsor (PeriodGroup ω c) (P i)]
  (rM : ∀ s, T s) (r : ∀ i, P i) {FM : (Σ s, T s) → ℝ} {F : (Σ i, P i) → ℝ}
  (hFM : ∀ s γ (D : T s), FM ⟨s, γ +ᵥ D⟩ = FM ⟨s, D⟩ - (-area ω c) γ)
  (hF : ∀ i γ (D : P i), F ⟨i, γ +ᵥ D⟩ = F ⟨i, D⟩ - (-area ω c) γ)
  {ν : (Σ s, T s) → ℤ} {μ : (Σ i, P i) → ℤ}
  (hν : ∀ s γ (D : T s), ν ⟨s, γ +ᵥ D⟩ = degree ω c γ + ν ⟨s, D⟩)
  (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩)
  (n : ℤ) (DM : κ → κ → NovikovSeries R G ωG) (D : ι → ι → NovikovSeries R G ωG) {CM C : ℝ}
  (hδM : ∀ p p',
    mapKernelOfMatrix rM rM (fun s t => coefficientComparison q hq (DM s t)) p p' ≠ 0 →
      FM p' ≤ FM p + CM)
  (hδ : ∀ p p', mapKernelOfMatrix r r (fun i k => coefficientComparison q hq (D i k)) p p' ≠ 0 →
    F p' ≤ F p + C)
  (Φ : κ → ι → NovikovSeries R G ωG) (Ψ : ι → κ → NovikovSeries R G ωG)
  (M : κ → κ → κ → NovikovSeries R G ωG) (Q : ι → ι → ι → NovikovSeries R G ωG) {CMQ CQ : ℝ}
  (hnM : ∀ p₁ p₂ p₀,
    kernelOfMatrix rM rM rM (fun s t l => coefficientComparison q hq (M s t l)) p₁ p₂ p₀ ≠ 0 →
      FM p₀ ≤ FM p₁ + FM p₂ + CMQ)
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r r r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F p₀ ≤ F p₁ + F p₂ + CQ)
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n)
  (hL : ∀ i j l, ∑ k, Q i j k * D k l =
    ∑ k, D i k * Q k j l + negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * Q i k l)
  (hΦ : ∀ s i, ∀ A ∈ (Φ s i).support, μ ⟨i, r i⟩ - degree ω c (q A) = ν ⟨s, rM s⟩)
  (hΦD : ∀ s i, ∑ k, Φ s k * D k i = ∑ t, DM s t * Φ t i)
  (hC : ∃ K : κ → κ → κ → NovikovSeries R G ωG,
    (∀ s t l, ∀ A ∈ (K s t l).support,
      ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨s, rM s⟩ + ν ⟨t, rM t⟩ - n + 1) ∧
    ∀ s t l, ∑ i, ∑ j, Φ s i * Φ t j * ∑ k, Q i j k * Ψ k l - M s t l =
      ∑ m, K s t m * DM m l + ∑ m, DM s m * K m t l +
        negOnePowCast R (n - ν ⟨s, rM s⟩) • ∑ m, DM t m * K s m l)
  [DecidableEq ι]
  (hΦΨ : ∃ Y : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (Y i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ s, Ψ i s * Φ s l - (if i = l then 1 else 0) =
      ∑ m, Y i m * D m l + ∑ m, D i m * Y m l)

include hν hμ hQ hL hΦ hΦD hC hΦΨ in
/-- **Multiplicativity of the PSS map of class-indexed counts on cocycles.** Under the comparison
identity of the comparison family and the module homotopy `Φ ∘ Ψ ≃ 1`, the PSS map sends the
Morse quantum product of two Morse cocycles to the pair-of-pants product of their images, up to a
coboundary of the Floer differential: `Φ (a ⋆_M b) - Φ a ⋆ Φ b` is a coboundary. -/
private theorem countMap_kernelProduct_sub_mem_coboundaries {e f : ℤ} {a b : NovikovModule R FM}
    (ha : a ∈ (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cocycles
      (gradeBy R FM fun p => n - ν p) e)
    (hb : b ∈ (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cocycles
      (gradeBy R FM fun p => n - ν p) f) :
    countMap rM r q hq hFM hF Φ (kernelProduct hnM (kernelOfMatrix_mem hFM rM rM rM _) a b) -
        kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) (countMap rM r q hq hFM hF Φ a)
          (countMap rM r q hq hFM hF Φ b) ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) (e + f) := by
  obtain ⟨K, hK, hCid⟩ := hC
  obtain ⟨Y, hY, hinv⟩ := hΦΨ
  rw [← neg_sub]
  refine neg_mem ?_
  rw [countMap_apply, countMap_apply, countMap_apply,
    ← novikovProductOfMatrix_eq_kernelProduct hFM hFM hFM rM rM rM _ hnM,
    ← novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ]
  exact novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries
    r r r rM rM rM q hq hF hF hF hFM hFM hFM hν Q M Φ Φ Ψ K DM DM DM n Φ D Y D D hμ hμ hμ hν hν
    hQ hΦ hΦ hΦ hY hK hL hΦD hΦD hCid (fun s k => (hΦD s k).symm) hinv hδM hδM hδ ha hb

variable (Z : κ → NovikovSeries R G ωG) (E : ι → NovikovSeries R G ωG)
  (hZ : ∀ s, ∀ A ∈ (Z s).support, ν ⟨s, rM s⟩ - degree ω c (q A) = n)
  (hE : ∀ i, ∀ A ∈ (E i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n)
  (hZD : ∀ l, ∑ s, Z s * DM s l = 0) (hED : ∀ l, ∑ i, E i * D i l = 0)
  [DecidableEq κ]
  (hone_mulM : ∃ K : κ → κ → NovikovSeries R G ωG,
    (∀ t l, ∀ A ∈ (K t l).support, ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨t, rM t⟩ + 1) ∧
    ∀ t l, ∑ s, Z s * M s t l - (1 : Matrix κ κ (NovikovSeries R G ωG)) t l =
      ∑ m, K t m * DM m l + ∑ m, DM t m * K m l)
  (hmul_one : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)
  (hΨ : ∀ i s, ∀ A ∈ (Ψ i s).support, ν ⟨s, rM s⟩ - degree ω c (q A) = μ ⟨i, r i⟩)
  (hΨD : ∀ i s, ∑ t, Ψ i t * DM t s = ∑ k, D i k * Ψ k s)

include hν hμ hδM hnM hnQ hQ hL hΦ hΦD hC hΦΨ hZ hZD hone_mulM hE hED hmul_one hΨ hΨD in
/-- **The PSS image of the fundamental cycle is the unit cycle.** Let `z` be the combination of the
Morse fundamental cycle `Z`, a left unit of the Morse quantum product up to homotopy, and `e` the
combination of the counts `E` of PSS planes, a right unit of the pair-of-pants product up to
homotopy. Under the comparison identity and the module PSS identities saying that `Φ` and `Ψ` are
chain maps and that `Φ ∘ Ψ` is homotopic to the identity, the PSS image `Φ z` differs from `e` by
a coboundary of the Floer differential. -/
theorem novikovMapOfMatrix_coordinates_symm_coefficientComparison_sub_mem_coboundaries :
    novikovMapOfMatrix hFM hF rM r (fun s i => coefficientComparison q hq (Φ s i))
        ((coordinates hFM rM).symm fun s => coefficientComparison q hq (Z s)) -
      (coordinates hF r).symm (fun i => coefficientComparison q hq (E i)) ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) 0 := by
  rw [← countMap_apply]
  exact LinearMap.sub_mem_coboundaries_of_surjective_cohomologyMap
    (kernelProduct hnM (kernelOfMatrix_mem hFM rM rM rM _)) _
    (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq rM hFM hν n DM hδM Z hZ hZD)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right rM q hq hFM rM hFM hν DM hδM M hnM
      Z hone_mulM)
    (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL) _
    (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (countMap rM r q hq hFM hF Φ) (countMap_mem_gradeBy rM r q hq hFM hF hν hμ Φ hΦ)
    (fun {_} {a} _ => kernelMap_countMap rM r q hq hFM hF Φ DM D hδM hδ hΦD a)
    (fun ha hb => countMap_kernelProduct_sub_mem_coboundaries q hq rM r hFM hF hν hμ n DM D hδM hδ
      Φ Ψ M Q hnM hnQ hQ hL hΦ hΦD hC hΦΨ ha hb)
    (surjective_cohomologyMap_countMap rM r q hq hFM hF hν hμ Φ DM D hδM hδ n Ψ hΦ hΨ hΦD hΨD hΦΨ 0)

variable
  (hM : ∀ s t l, ∀ A ∈ (M s t l).support,
    ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨s, rM s⟩ + ν ⟨t, rM t⟩ - n)
  (hLM : ∀ s t l, ∑ k, M s t k * DM k l =
    ∑ k, DM s k * M k t l + negOnePowCast R (n - ν ⟨s, rM s⟩) • ∑ k, DM t k * M s k l)
  (hmul_oneM : ∃ K : κ → κ → NovikovSeries R G ωG,
    (∀ s l, ∀ A ∈ (K s l).support, ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨s, rM s⟩ + 1) ∧
    ∀ s l, ∑ t, Z t * M s t l - (1 : Matrix κ κ (NovikovSeries R G ωG)) s l =
      ∑ m, K s m * DM m l + ∑ m, DM s m * K m l)
  (hassocM : ∃ K : κ → κ → κ → κ → NovikovSeries R G ωG,
    (∀ s t u l, ∀ A ∈ (K s t u l).support,
      ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨s, rM s⟩ + ν ⟨t, rM t⟩ + ν ⟨u, rM u⟩ - 2 * n + 1) ∧
    ∀ s t u l, ∑ v, M s t v * M v u l - ∑ v, M t u v * M s v l =
      ∑ m, K s t u m * DM m l + ∑ m, DM s m * K m t u l +
        negOnePowCast R (n - ν ⟨s, rM s⟩) • ∑ m, DM t m * K s m u l +
        negOnePowCast R (n - ν ⟨s, rM s⟩ + (n - ν ⟨t, rM t⟩)) • ∑ m, DM u m * K s t m l)
  (hone_mul : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1) ∧
    ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
  (hassoc : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q i j t * Q t k l - ∑ u, Q j k u * Q i u l =
      ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
        negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)
  (hΨΦ : ∃ Y : κ → κ → NovikovSeries R G ωG,
    (∀ s l, ∀ A ∈ (Y s l).support, ν ⟨l, rM l⟩ - degree ω c (q A) = ν ⟨s, rM s⟩ + 1) ∧
    ∀ s l, ∑ i, Φ s i * Ψ i l - (if s = l then 1 else 0) =
      ∑ m, Y s m * DM m l + ∑ m, DM s m * Y m l)

/-- **Multiplicative PSS for class-indexed counts.** Let the Morse counts (trajectories `DM`, the
Morse quantum product `M`, the fundamental cycle `Z`) and the Floer counts (cylinders `D`, pairs of
pants `Q`, PSS planes `E`) each satisfy the hypotheses of `TauCeti.Floer.cohomologyGRingOfCounts`,
so that their degree-wise cohomologies are algebras over the ground ring. Let `Φ` and `Ψ` count
rigid PSS half-cylinders in the two directions, preserving the index (`hΦ`, `hΨ`), and suppose that
the module PSS isomorphism gives the identities saying that `Φ` and `Ψ` are chain maps (`hΦD`,
`hΨD`) and that `Ψ ∘ Φ` and `Φ ∘ Ψ` are homotopic to the identities (`hΨΦ`, `hΦΨ`), and that the
comparison family gives the comparison identity `hC`, each homotopy counting configurations which
lower the cochain degree by one. Then the maps induced by `Φ` on cohomology form an isomorphism of
algebras over the ground ring from the cohomology ring of the Morse counts to that of the Floer
counts. -/
def pssAlgEquivOfCounts :
    letI := cohomologyGRingOfCounts q hq rM hFM hν n DM hδM M hnM hM hLM Z hZ hZD hone_mulM
      hmul_oneM hassocM
    letI := cohomologyGAlgebraOfCounts q hq rM hFM hν n DM hδM M hnM hM hLM Z hZ hZD hone_mulM
      hmul_oneM hassocM
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGAlgebraOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    (⨁ k, (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cohomology
        (gradeBy R FM fun p => n - ν p) k) ≃ₐ[R]
      ⨁ k, (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
        (gradeBy R F fun p => n - μ p) k :=
  algEquivOfCounts q hq rM r hFM hF hν hμ n DM D hδM hδ M Q hnM hnQ hM hQ hLM hL Z E hZ hE hZD hED
    hone_mulM hone_mul hmul_oneM hmul_one hassocM hassoc Φ Ψ hΦ hΨ hΦD hΨD
    (fun ha hb => countMap_kernelProduct_sub_mem_coboundaries q hq rM r hFM hF hν hμ n DM D hδM hδ
      Φ Ψ M Q hnM hnQ hQ hL hΦ hΦD hC hΦΨ ha hb)
    hΨΦ hΦΨ

/-- The PSS isomorphism sends the class of a Morse cocycle `a` to the class of its image `Φ a`
under the map of the PSS counts. -/
theorem pssAlgEquivOfCounts_of_mk {k : ℤ}
    (a : (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cocycles
      (gradeBy R FM fun p => n - ν p) k)
    (b : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) k)
    (hab : novikovMapOfMatrix hFM hF rM r (fun s i => coefficientComparison q hq (Φ s i)) a = b) :
    pssAlgEquivOfCounts q hq rM r hFM hF hν hμ n DM D hδM hδ Φ Ψ M Q hnM hnQ hQ hL hΦ hΦD hC hΦΨ
        Z E hZ hE hZD hED hone_mulM hmul_one hΨ hΨD hM hLM hmul_oneM hassocM hone_mul hassoc hΨΦ
        (of _ k (Submodule.Quotient.mk a)) =
      of (fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
        (gradeBy R F fun p => n - μ p) k) k (Submodule.Quotient.mk b) :=
  algEquivOfCounts_of_mk q hq rM r hFM hF hν hμ n DM D hδM hδ M Q hnM hnQ hM hQ hLM hL Z E hZ hE hZD
    hED hone_mulM hone_mul hmul_oneM hmul_one hassocM hassoc Φ Ψ hΦ hΨ hΦD hΨD _ hΨΦ hΦΨ a b hab

/-- The inverse of the PSS isomorphism is induced by the PSS counts `Ψ` in the opposite
direction: it sends the class of a Floer cocycle `b` to the class of the Morse cocycle `Ψ b`. -/
theorem pssAlgEquivOfCounts_symm_of_mk {k : ℤ}
    (b : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) k)
    (a : (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cocycles
      (gradeBy R FM fun p => n - ν p) k)
    (hba : novikovMapOfMatrix hF hFM r rM (fun i s => coefficientComparison q hq (Ψ i s)) b = a) :
    letI := cohomologyGRingOfCounts q hq rM hFM hν n DM hδM M hnM hM hLM Z hZ hZD hone_mulM
      hmul_oneM hassocM
    letI := cohomologyGAlgebraOfCounts q hq rM hFM hν n DM hδM M hnM hM hLM Z hZ hZD hone_mulM
      hmul_oneM hassocM
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGAlgebraOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    (pssAlgEquivOfCounts q hq rM r hFM hF hν hμ n DM D hδM hδ Φ Ψ M Q hnM hnQ hQ hL hΦ hΦD hC hΦΨ
        Z E hZ hE hZD hED hone_mulM hmul_one hΨ hΨD hM hLM hmul_oneM hassocM hone_mul hassoc
        hΨΦ).symm (of _ k (Submodule.Quotient.mk b)) =
      of (fun k => (kernelMap hδM (mapKernelOfMatrix_mem hFM rM rM _)).cohomology
        (gradeBy R FM fun p => n - ν p) k) k (Submodule.Quotient.mk a) :=
  algEquivOfCounts_symm_of_mk q hq rM r hFM hF hν hμ n DM D hδM hδ M Q hnM hnQ hM hQ hLM hL Z E hZ
    hE hZD hED hone_mulM hone_mul hmul_oneM hmul_one hassocM hassoc Φ Ψ hΦ hΨ hΦD hΨD _ hΨΦ hΦΨ b a
    hba

end TauCeti.Floer

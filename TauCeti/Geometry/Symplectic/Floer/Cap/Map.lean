/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CoefficientComparison
public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.MapOfMatrix

/-!
# Maps of class-indexed counts on capped generators

Fix finitely many orbits for the source and the target of a map, with capped generators `P₁`,
`P₀` forming torsors under the period group `Γ = PeriodGroup ω c`, and reference caps `r₁`, `r₀`.
A map between them, such as a PSS map, a continuation map or a homotopy between maps, is counted
class by class: for orbits `i` and `k` the counts are recorded by a generating series
`Φ i k = ∑_A N_A q^A` in a common class group `G` mapping to `Γ` by an area-preserving homomorphism
`q`. The matrix `fun i k => coefficientComparison q hq (Φ i k)` sends these series to the Floer
Novikov ring by the coefficient comparison `q^A ↦ e^(-q A)` of
`TauCeti.Floer.coefficientComparison`, and its map (`TauCeti.NovikovModule.novikovMapOfMatrix`) is
a linear map of the completed capped modules. This file proves:

* **The kernel.** Its coefficient at `(D₁, D₀)` is the sum of the counts over the classes `A` with
  `q A = (D₁ - r₁) - (D₀ - r₀)`
  (`TauCeti.Floer.mapKernelOfMatrix_coefficientComparison_apply`).
* **Degree from the index.** Under the index condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) - ε` and the
  recapping law `μ(γ # D) = 2 c₁(γ) + μ(D)`, the kernel changes the grading by `-ε`
  (`TauCeti.Floer.grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero`), so the map
  shifts the cochain degree `n - μ` and its residues by `ε`
  (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_mem_map_cochain_gradeBy`).
* **Chain maps.** If the series obey the identity `∑ₖ Φᵢₖ Dₖₖ' = ∑ᵢ' Eᵢᵢ' Φᵢ'ₖ'` with series
  `D` and `E` of differentials, the map intertwines the differentials
  (`TauCeti.Floer.novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_comm`).

The index and boundary-count hypotheses are the ones the geometric moduli spaces are to supply; no
moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology and the Piunikhin–Salamon–Schwarz isomorphism.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section MapKernel

variable [Semiring R]

/-- **The kernel of class-indexed counts of a map on capped generators.** Its coefficient at
capped generators `D₁` and `D₀` of the orbits `i` and `k` is the finite sum of the counts over all
classes `A` with `q A = (D₁ - r₁) - (D₀ - r₀)`. -/
theorem mapKernelOfMatrix_coefficientComparison_apply
    (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) {i : ι₁} {k : ι₀} (D₁ : P₁ i) (D₀ : P₀ k) :
    mapKernelOfMatrix r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) ⟨i, D₁⟩ ⟨k, D₀⟩ =
      ∑ᶠ A ∈ q ⁻¹' {(D₁ -ᵥ r₁ i) - (D₀ -ᵥ r₀ k)}, (Φ i k).coeff A := by
  -- The matrix of comparisons is a function of two indices, so the entry formula is applied as a
  -- term rather than rewritten.
  refine (mapKernelOfMatrix_apply r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) D₁
    D₀).trans ?_
  rw [coefficientComparison_apply, coeff_map]
  refine finsum_mem_congr ?_ fun _ _ => rfl
  ext A
  simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply,
    neg_eq_iff_eq_neg, neg_sub]

variable {μ₁ : (Σ i, P₁ i) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {ε : ℤ} {Φ : ι₁ → ι₀ → NovikovSeries R G ωG}

include hμ₁ hμ₀

/-- **Degree of the kernel of a map from the index.** If the gradings obey the recapping law and
every class with nonzero count satisfies the index condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) - ε`
relative to the reference caps, then the kernel changes the grading by `-ε` at all capped
generators. -/
theorem grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero
    (hΦ : ∀ i k, ∀ A ∈ (Φ i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ - ε)
    (p₁ : Σ i, P₁ i) (p₀ : Σ k, P₀ k)
    (h : mapKernelOfMatrix r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) p₁ p₀ ≠ 0) :
    μ₀ p₀ = μ₁ p₁ - ε := by
  obtain ⟨i, D₁⟩ := p₁
  obtain ⟨k, D₀⟩ := p₀
  rw [mapKernelOfMatrix_coefficientComparison_apply] at h
  obtain ⟨A, hA, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  have hd := hΦ i k A (mem_support.2 hne)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hA
  rw [hA, map_sub] at hd
  have e₁ := hμ₁ i (D₁ -ᵥ r₁ i) (r₁ i)
  have e₀ := hμ₀ k (D₀ -ᵥ r₀ k) (r₀ k)
  rw [vsub_vadd] at e₁ e₀
  linarith

end MapKernel

section MapGrading

variable [CommSemiring R] {μ₁ : (Σ i, P₁ i) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {ε : ℤ} {Φ : ι₁ → ι₀ → NovikovSeries R G ωG}

include hμ₁ hμ₀

/-- **A map of rigid counts shifts the cochain degree by `ε`.** Under the index condition of
`TauCeti.Floer.grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero`, the map of
class-indexed counts sends a combination of degree `e` in an additive image `f` of the cochain
degree `n - μ₁` to one of degree `e + f ε` in the same image of `n - μ₀`; for `f` the quotient
map modulo the degrees of the period group this is the residue grading. PSS maps have `ε = 0`,
and the homotopies between them have `ε = -1`. -/
theorem novikovMapOfMatrix_coefficientComparison_mem_map_cochain_gradeBy [Finite ι₁] [Finite ι₀]
    {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    (hΦ : ∀ i k, ∀ A ∈ (Φ i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ - ε)
    {D : Type*} [AddMonoid D] (f : ℤ →+ D) {n : ℤ} {e : D} {a : NovikovModule R F₁}
    (ha : a ∈ gradeBy R F₁ (fun p => f (n - μ₁ p)) e) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a ∈
      gradeBy R F₀ (fun p => f (n - μ₀ p)) (e + f ε) := by
  obtain ⟨C, hm⟩ := exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (Φ i k))
  rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hm]
  refine kernelMap_mem_gradeBy hm _ (fun p₁ p₀ h => ?_) ha
  rw [grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero r₁ r₀ q hq hμ₁ hμ₀ hΦ p₁ p₀ h,
    ← map_add]
  congr 1
  ring

/-- A map of rigid class-indexed counts shifts the cochain degree `n - μ` by `ε`. -/
theorem novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy [Finite ι₁] [Finite ι₀]
    {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    (hΦ : ∀ i k, ∀ A ∈ (Φ i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ - ε)
    {n e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a ∈
      gradeBy R F₀ (fun p => n - μ₀ p) (e + ε) :=
  novikovMapOfMatrix_coefficientComparison_mem_map_cochain_gradeBy r₁ r₀ q hq hμ₁ hμ₀ hF₁ hF₀ hΦ
    (AddMonoidHom.id ℤ) ha

end MapGrading

section ChainMap

variable [CommSemiring R]

/-- **Chain maps of class-indexed counts.** If the generating series of a map `Φ` and of
endomorphisms `D` of its target and `E` of its source obey the identity
`∑ᵢ Φₛᵢ Dᵢᵢ' = ∑ₛ' Eₛₛ' Φₛ'ᵢ'` in `G`-indexed series, which is the count, class by class, of the
ends of one-dimensional moduli spaces saying that `Φ` is a chain map, then on the completed capped
modules `D (Φ a) = Φ (E a)`. -/
theorem novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_comm [Fintype ι₁]
    [Fintype ι₀] {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) (D : ι₀ → ι₀ → NovikovSeries R G ωG)
    (E : ι₁ → ι₁ → NovikovSeries R G ωG)
    (hΦ : ∀ i k', ∑ k, Φ i k * D k k' = ∑ i', E i i' * Φ i' k') (a : NovikovModule R F₁) :
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D k k'))
        (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a) =
      novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k))
        (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i i' => coefficientComparison q hq (E i i')) a) := by
  -- The matrices of comparisons are named as matrices so that their products are matrix
  -- products. The count identity is a matrix identity, which the ring homomorphism
  -- `coefficientComparison` carries to these matrices.
  set Φ' : Matrix ι₁ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i k => coefficientComparison q hq (Φ i k)
  set D' : Matrix ι₀ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun k k' => coefficientComparison q hq (D k k')
  set E' : Matrix ι₁ ι₁ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i i' => coefficientComparison q hq (E i i')
  have hm : Φ' * D' = E' * Φ' := by
    have h := congrArg (Matrix.map · (coefficientComparison q hq))
      (Matrix.ext hΦ : Matrix.of Φ * Matrix.of D = Matrix.of E * Matrix.of Φ)
    rwa [Matrix.map_mul, Matrix.map_mul] at h
  have h := congrArg (fun A => novikovMapOfMatrix hF₁ hF₀ r₁ r₀ A a) hm
  simpa only [novikovMapOfMatrix_mul hF₁ hF₀ hF₀ r₁ r₀ r₀,
    novikovMapOfMatrix_mul hF₁ hF₀ hF₁ r₁ r₀ r₁, LinearMap.comp_apply] using h

end ChainMap

end TauCeti.Floer

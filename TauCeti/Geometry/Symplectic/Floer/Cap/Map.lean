/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Graded
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
* **Homotopies.** If the series of two maps `Φ`, `Φ'` and of a map `Y` obey
  `Φᵢₖ - Φ'ᵢₖ = ∑ₘ Yᵢₘ D₀ₘₖ + ∑ₘ D₁ᵢₘ Yₘₖ`, then `Φ - Φ' = D₀ Y + Y D₁` on the completed modules
  (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_sub_eq_add`); when `Y` lowers the
  cochain degree by one, `Φ a - Φ' a` is a coboundary for every cocycle `a`
  (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries`), so `Φ` and `Φ'`
  induce the same map on cohomology. In particular, if `Ψ` is a module inverse of `Φ` up to such a
  homotopy, `Ψ (Φ a) - a` is a coboundary for every cocycle `a`
  (`novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries`). Applied
  once to `(Φ, Ψ)` and once to `(Ψ, Φ)`, each with its own homotopy, this supplies the two
  hypotheses `hgf` and `hfg` under which `LinearMap.cohomologyEquiv` makes a PSS map an
  isomorphism of cohomology.
* **Change of reference caps.** Moving the reference caps to `q gₗ # rₗ` for lifts `g₁, g₀ ∈ G`
  changes the class of each counted configuration relative to them by `g₀ - g₁`. With the
  generating series multiplied by `q^(g₀ - g₁)` accordingly, the kernel, hence the map, is
  unchanged (`TauCeti.Floer.mapKernelOfMatrix_coefficientComparison_vadd`,
  `TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_vadd`). This is the Floer form of
  `TauCeti.NovikovModule.mapKernelOfMatrix_vadd_single_mul`, through `q^A ↦ e^(-q A)`.

The index and boundary-count hypotheses are the ones the geometric moduli spaces are to supply; no
moduli space, orientation or count is constructed here.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, for the independence from the choice of reference
  caps.
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

section Monoid

variable {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
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

/-- The map of the comparison of the identity matrix of class-indexed series is the identity:
the stationary cylinders act as the identity on the completed capped module. -/
@[simp]
theorem novikovMapOfMatrix_coefficientComparison_one_apply [Finite ι₁] [DecidableEq ι₁]
    {F₁ : (Σ i, P₁ i) → ℝ} (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (x : NovikovModule R F₁) :
    letI := module (R := R) hF₁
    novikovMapOfMatrix hF₁ hF₁ r₁ r₁
        (fun i i' => coefficientComparison q hq ((1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i i'))
        x =
      x := by
  let := module (R := R) hF₁
  have h1 : (fun i i' =>
      coefficientComparison q hq ((1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i i')) =
      (1 : Matrix ι₁ ι₁ _) :=
    Matrix.map_one (coefficientComparison q hq) (map_zero _) (map_one _)
  rw [h1, novikovMapOfMatrix_one, LinearMap.id_apply]

end ChainMap

section Homotopy

variable [CommRing R] [Fintype ι₁] [Fintype ι₀] {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

/-- **Homotopies of class-indexed counts.** If the generating series of two maps `Φ` and `Φ'`, of
a map `Y` and of endomorphisms `D₁` of the source and `D₀` of the target obey the identity
`Φᵢₖ - Φ'ᵢₖ = ∑ₘ Yᵢₘ D₀ₘₖ + ∑ₘ D₁ᵢₘ Yₘₖ` in `G`-indexed series, which is the count, class by
class, of the ends of the one-dimensional moduli spaces of a family interpolating between `Φ` and
`Φ'`, then on the completed capped modules `Φ a - Φ' a = D₀ (Y a) + Y (D₁ a)`. -/
theorem novikovMapOfMatrix_coefficientComparison_sub_eq_add
    (Φ Φ' Y : ι₁ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hY : ∀ i k, Φ i k - Φ' i k = ∑ m, Y i m * D₀ m k + ∑ m, D₁ i m * Y m k)
    (a : NovikovModule R F₁) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ' i k)) a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k'))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Y i k)) a) +
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Y i k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i i' => coefficientComparison q hq (D₁ i i'))
            a) := by
  -- As for chain maps, the count identity is a matrix identity carried by the ring homomorphism
  -- `coefficientComparison` to the matrices of comparisons, whose maps compose.
  set Φc : Matrix ι₁ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i k => coefficientComparison q hq (Φ i k)
  set Φc' : Matrix ι₁ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i k => coefficientComparison q hq (Φ' i k)
  set Yc : Matrix ι₁ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i k => coefficientComparison q hq (Y i k)
  set D₁c : Matrix ι₁ ι₁ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i i' => coefficientComparison q hq (D₁ i i')
  set D₀c : Matrix ι₀ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun k k' => coefficientComparison q hq (D₀ k k')
  have hm : Φc = Φc' + (Yc * D₀c + D₁c * Yc) := by
    have h := congrArg (Matrix.map · (coefficientComparison q hq))
      (Matrix.ext hY : Matrix.of Φ - Matrix.of Φ' =
        Matrix.of Y * Matrix.of D₀ + Matrix.of D₁ * Matrix.of Y)
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), Matrix.map_mul,
      Matrix.map_mul] at h
    exact eq_add_of_sub_eq' h
  rw [sub_eq_iff_eq_add', hm, novikovMapOfMatrix_add, novikovMapOfMatrix_add,
    novikovMapOfMatrix_mul hF₁ hF₀ hF₀ r₁ r₀ r₀, novikovMapOfMatrix_mul hF₁ hF₀ hF₁ r₁ r₀ r₁]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]

variable {μ₁ : (Σ i, P₁ i) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)

include hμ₁ hμ₀ in
/-- **Homotopic maps of class-indexed counts agree on cocycles up to coboundaries.** Under the
identity of `TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_sub_eq_add`, suppose that every
class counted by `Y` satisfies the index condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + 1`, so that `Y`
lowers the cochain degree `n - μ` by one. Then for every cocycle `a` of `D₁` of cochain degree `e`,
`Φ a - Φ' a` is a coboundary of `D₀` of cochain degree `e`. The endomorphisms are the ground-ring
linear maps of their counts, for any potential bounds of their kernels. -/
theorem novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries
    (Φ Φ' Y : ι₁ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hYdeg : ∀ i k, ∀ A ∈ (Y i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hY : ∀ i k, Φ i k - Φ' i k = ∑ m, Y i m * D₀ m k + ∑ m, D₁ i m * Y m k) {C₁ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i i' => coefficientComparison q hq (D₁ i i')) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k')) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {n e : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ' i k)) a ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) e := by
  -- The maps are written as the ground-ring linear maps of their kernels, which are the maps of
  -- the generic homotopy lemma.
  obtain ⟨_, hΦ⟩ := exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (Φ i k))
  obtain ⟨_, hΦ'⟩ := exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (Φ' i k))
  obtain ⟨_, hYm⟩ := exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (Y i k))
  rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hΦ,
    novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hΦ']
  refine LinearMap.sub_mem_coboundaries_of_homotopy
    (kernelMap hYm (mapKernelOfMatrix_mem hF₀ r₁ r₀ _)) (fun {b} hb => ?_) (fun {b} _ => ?_) ha
  · -- `Y` lowers the cochain degree by one.
    rw [← novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hYm]
    simpa only [← sub_eq_add_neg] using novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy
      r₁ r₀ q hq hμ₁ hμ₀ hF₁ hF₀ (ε := -1)
      (fun i k A hA => by rw [sub_neg_eq_add]; exact hYdeg i k A hA) hb
  · simp only [← novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hΦ,
      ← novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hΦ',
      ← novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hYm,
      ← novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀,
      ← novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁]
    exact novikovMapOfMatrix_coefficientComparison_sub_eq_add r₁ r₀ q hq hF₁ hF₀ Φ Φ' Y D₁ D₀ hY b

include hμ₁ in
/-- **Module inverses of class-indexed counts on cocycles.** Let `Φ` be the generating series of a
map out of the capped generators `P₁` and `Ψ` those of a map back to them, such as the PSS maps
in the two directions, let `D₁` be those of the differential of `P₁`, and let `Y` be those of the
rigid members of the family whose two ends are the broken composite of `Φ` and `Ψ` and the
identity. Suppose that the series obey the identity

`∑ₖ Φᵢₖ Ψₖᵢ' - [i = i'] = ∑ₘ Yᵢₘ D₁ₘᵢ' + ∑ₘ D₁ᵢₘ Yₘᵢ'`

in `G`-indexed series and that `Y` lowers the cochain degree `n - μ₁` by one, as in
`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries`. Then for every
cocycle `a` of `D₁` of cochain degree `e`, `Ψ (Φ a) - a` is a coboundary of `D₁` of cochain degree
`e`: the composite of the two maps is the identity on cohomology. -/
theorem novikovMapOfMatrix_novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries
    [DecidableEq ι₁] (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) (Ψ : ι₀ → ι₁ → NovikovSeries R G ωG)
    (Y D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (hYdeg : ∀ i i', ∀ A ∈ (Y i i').support,
      μ₁ ⟨i', r₁ i'⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hinv : ∀ i i', ∑ k, Φ i k * Ψ k i' - (if i = i' then 1 else 0) =
      ∑ m, Y i m * D₁ m i' + ∑ m, D₁ i m * Y m i') {C₁ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i i' => coefficientComparison q hq (D₁ i i')) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    {n e : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e) :
    novikovMapOfMatrix hF₀ hF₁ r₀ r₁ (fun k i => coefficientComparison q hq (Ψ k i))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) a) -
        a ∈
      (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).coboundaries
        (gradeBy R F₁ fun p => n - μ₁ p) e := by
  have h := novikovMapOfMatrix_coefficientComparison_sub_mem_coboundaries r₁ r₁ q hq hF₁ hF₁ hμ₁
    hμ₁ (fun i i' => ∑ k, Φ i k * Ψ k i') (fun i i' => if i = i' then 1 else 0) Y D₁ D₁ hYdeg hinv
    hδ₁ hδ₁ ha
  -- The comparisons of the composite counts and of the identity counts are the matrix product
  -- and the identity matrix, whose maps are the composite and the identity.
  set Φc : Matrix ι₁ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun i k => coefficientComparison q hq (Φ i k)
  set Ψc : Matrix ι₀ ι₁ (NovikovSeries R (PeriodGroup ω c) (-area ω c)) :=
    fun k i => coefficientComparison q hq (Ψ k i)
  have hΦΨ : (fun i i' => coefficientComparison q hq (∑ k, Φ i k * Ψ k i')) = Φc * Ψc := by
    funext i i'
    rw [Matrix.mul_apply, map_sum]
    simp only [_root_.map_mul, Φc, Ψc]
  have h₁ : (fun i i' => coefficientComparison q hq (if i = i' then 1 else 0)) =
      (1 : Matrix ι₁ ι₁ (NovikovSeries R (PeriodGroup ω c) (-area ω c))) := by
    funext i i'
    simp only [apply_ite (coefficientComparison q hq), _root_.map_one, map_zero, Matrix.one_apply]
  let := module (R := R) hF₁
  rwa [hΦΨ, h₁, novikovMapOfMatrix_mul hF₁ hF₁ hF₀ r₁ r₁ r₀, novikovMapOfMatrix_one,
    LinearMap.comp_apply, LinearMap.id_apply] at h

end Homotopy

end Monoid

section Reference

variable {G : Type*} [AddGroup G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

/-- **Change of reference caps.** Moving the reference caps to `q gₗ # rₗ` changes the class of a
counted configuration relative to the reference caps by `g₀ - g₁`, so the generating series become
`q^(g₀ - g₁) Φ`. The kernel on capped generators is unchanged. -/
theorem mapKernelOfMatrix_coefficientComparison_vadd [Semiring R]
    (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) (g₁ : ι₁ → G) (g₀ : ι₀ → G) :
    mapKernelOfMatrix (fun i => q (g₁ i) +ᵥ r₁ i) (fun k => q (g₀ k) +ᵥ r₀ k)
        (fun i k => coefficientComparison q hq (NovikovSeries.single (g₀ k - g₁ i) 1 * Φ i k)) =
      mapKernelOfMatrix r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) := by
  refine Eq.trans ?_ (mapKernelOfMatrix_vadd_single_mul r₁ r₀
    (fun i k => coefficientComparison q hq (Φ i k)) (fun i => q (g₁ i)) fun k => q (g₀ k))
  congr 1
  ext i k
  simp [map_sub]

/-- **A map of class-indexed counts does not depend on the reference caps.** Moving the reference
caps to `q gₗ # rₗ` and the generating series to `q^(g₀ - g₁) Φ` gives the same map on capped
generators. This applies to the differentials, continuation and PSS maps and the homotopies between
them. -/
theorem novikovMapOfMatrix_coefficientComparison_vadd [CommSemiring R] [Finite ι₁] [Finite ι₀]
    {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) (g₁ : ι₁ → G) (g₀ : ι₀ → G) :
    novikovMapOfMatrix hF₁ hF₀ (fun i => q (g₁ i) +ᵥ r₁ i) (fun k => q (g₀ k) +ᵥ r₀ k)
        (fun i k => coefficientComparison q hq (NovikovSeries.single (g₀ k - g₁ i) 1 * Φ i k)) =
      novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) := by
  refine Eq.trans ?_ (novikovMapOfMatrix_vadd_single_mul hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (Φ i k)) (fun i => q (g₁ i)) fun k => q (g₀ k))
  congr 1
  ext i k
  simp [map_sub]

end Reference

end TauCeti.Floer

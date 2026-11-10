/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.KernelMap
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Novikov-linear maps given by matrices of Novikov series

Let each of `S₁ = Σ i, P₁ i` and `S₀ = Σ k, P₀ k` be a finite disjoint union of torsors under a
commutative group `H` of periods `N : H →+ ℝ`, with equivariant potentials, and fix a reference
generator in each orbit. An invariant kernel `m : S₁ → S₀ → R`, one that is unchanged when the input
and the output are translated by the same element, gives a Novikov-linear map of completed
combinations (`TauCeti.NovikovModule.novikovKernelMap`). In the reference coordinates it is
multiplication by the matrix whose `(i, k)` entry is the Novikov series of coefficients, in the
orbit `k`, of the output of `m` at the reference generator of the orbit `i`
(`TauCeti.NovikovModule.coordinates_kernelMap`).

This file constructs the converse. Every matrix `M` of Novikov series is the matrix of an
invariant kernel (`TauCeti.NovikovModule.mapKernelOfMatrix`): its coefficient on generators in
the orbits `i` and `k` is the coefficient of `M i k` at the displacement of the output from its
reference generator minus the displacement of the input. With finitely many orbits this kernel
obeys a potential bound, so it has a Novikov-linear map
(`TauCeti.NovikovModule.novikovMapOfMatrix`), given in reference coordinates by
`cₖ = ∑ᵢ aᵢ Mᵢₖ`. Relative to the reference bases it is Mathlib's `Matrix.toLin` of the transpose
of `M` (`TauCeti.NovikovModule.novikovMapOfMatrix_eq_toLin`), so it is linear in `M`, composition
of maps is multiplication of matrices (`TauCeti.NovikovModule.novikovMapOfMatrix_mul`), and the
identity matrix gives the identity map.

This is the one-input counterpart of `TauCeti.NovikovModule.kernelOfMatrix` and
`TauCeti.NovikovModule.novikovProductOfMatrix`. In Floer theory the generators are capped
orbits, the entries are the generating series `∑_A #M(x, y; A) e^(-A)` of rigid Floer cylinders
between reference capped orbits, and the maps are the differentials, continuation maps and chain
homotopies on the completed complexes. The potential bound of the kernel follows from lower
period bounds on the entries (`TauCeti.NovikovModule.potential_le_of_mapKernelOfMatrix_ne_zero`),
which is the form that the energy estimate takes for class-indexed counts.

## Main definitions

* `TauCeti.NovikovModule.mapKernelOfMatrix`: the invariant one-input kernel with a given matrix
  of Novikov series.
* `TauCeti.NovikovModule.novikovMapOfMatrix`: the Novikov-linear map of a finite matrix of
  Novikov series.

## Main results

* `TauCeti.NovikovModule.coordinates_mapKernelOfMatrix`,
  `TauCeti.NovikovModule.mapKernelOfMatrix_coordinates`: invariant kernels and matrices of
  Novikov series determine each other.
* `TauCeti.NovikovModule.coordinates_novikovMapOfMatrix`: the matrix formula for the map of a
  matrix.
* `TauCeti.NovikovModule.novikovMapOfMatrix_eq_toLin`: the map of a matrix is `Matrix.toLin` of
  its transpose for the reference bases.
* `TauCeti.NovikovModule.novikovMapOfMatrix_add`, `TauCeti.NovikovModule.novikovMapOfMatrix_smul`:
  the map of a matrix is linear in the matrix.
* `TauCeti.NovikovModule.novikovMapOfMatrix_mul`, `TauCeti.NovikovModule.novikovMapOfMatrix_one`:
  the map of a product of matrices is the composite of their maps, and the identity matrix gives
  the identity.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2, on completed modules over Novikov rings.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

variable {R H ι₁ ι₂ ι₀ : Type*} [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ j, AddTorsor H (P₂ j)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)

section Zero

variable [Zero R] (M : Matrix ι₁ ι₀ (NovikovSeries R H N))

/-- The one-input kernel with a given matrix `M` of Novikov series relative to reference
generators `r₁` and `r₀`. Its coefficient on generators `p₁` and `p₀` in the orbits `i` and `k` is
the coefficient of `M i k` at the displacement of `p₀` from `r₀ k` minus the displacement of `p₁`
from `r₁ i`. -/
def mapKernelOfMatrix (p₁ : Σ i, P₁ i) (p₀ : Σ k, P₀ k) : R :=
  (M p₁.1 p₀.1).coeff (p₀.2 -ᵥ r₀ p₀.1 - (p₁.2 -ᵥ r₁ p₁.1))

/-- The coefficient of the kernel of a matrix on generators in the orbits `i` and `k` is a
coefficient of the `(i, k)` entry. -/
@[simp]
theorem mapKernelOfMatrix_apply {i : ι₁} {k : ι₀} (p₁ : P₁ i) (p₀ : P₀ k) :
    mapKernelOfMatrix r₁ r₀ M ⟨i, p₁⟩ ⟨k, p₀⟩ = (M i k).coeff (p₀ -ᵥ r₀ k - (p₁ -ᵥ r₁ i)) :=
  (rfl)

/-- The kernel of a matrix is unchanged when its input and its output are translated by the same
element. -/
theorem mapKernelOfMatrix_vadd (g : H) (i : ι₁) (p₁ : P₁ i) (k : ι₀) (p₀ : P₀ k) :
    mapKernelOfMatrix r₁ r₀ M ⟨i, g +ᵥ p₁⟩ ⟨k, g +ᵥ p₀⟩ =
      mapKernelOfMatrix r₁ r₀ M ⟨i, p₁⟩ ⟨k, p₀⟩ := by
  simp only [mapKernelOfMatrix_apply, vadd_vsub_assoc, add_sub_add_left_eq_sub]

include hF₁ hF₀ in
/-- **Every finite matrix of Novikov series has a supported kernel.** With finitely many orbits,
the kernel of any matrix of Novikov series obeys a potential bound with some constant `C`, since
the periods of the support of each of the finitely many entries are bounded below. -/
theorem exists_potential_le_of_mapKernelOfMatrix_ne_zero [Finite ι₁] [Finite ι₀] :
    ∃ C, ∀ p₁ p₀, mapKernelOfMatrix r₁ r₀ M p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C := by
  choose b hb using fun q : ι₁ × ι₀ => (M q.1 q.2).bddBelow_image_support
  obtain ⟨C, hC⟩ := (Set.finite_range fun q : ι₁ × ι₀ =>
    F₀ ⟨q.2, r₀ q.2⟩ - F₁ ⟨q.1, r₁ q.1⟩ - b q).bddAbove
  refine ⟨C, fun ⟨i, p₁⟩ ⟨k, p₀⟩ h => ?_⟩
  have h₁ := hb (i, k) ⟨_, NovikovSeries.mem_support.2 h, rfl⟩
  have h₂ := hC ⟨(i, k), rfl⟩
  simp only [map_sub] at h₁ h₂
  rw [potential_eq_sub_vsub hF₁ r₁ i p₁, potential_eq_sub_vsub hF₀ r₀ k p₀]
  linarith

end Zero

section Semiring

variable [Semiring R]

include hF₀ in
/-- The outputs of the kernel of a matrix are completed combinations: in the output coordinates
relative to `r₀`, the output at `p₁` is the row `M i · e^u`, where `i` is the orbit of `p₁` and `u`
is the displacement of `p₁` from its reference generator. -/
theorem mapKernelOfMatrix_mem [Finite ι₀] (M : Matrix ι₁ ι₀ (NovikovSeries R H N))
    (p₁ : Σ i, P₁ i) : mapKernelOfMatrix r₁ r₀ M p₁ ∈ NovikovModule R F₀ := by
  have h : mapKernelOfMatrix r₁ r₀ M p₁ = ((coordinates hF₀ r₀).symm fun k =>
      M p₁.1 k * NovikovSeries.single (p₁.2 -ᵥ r₁ p₁.1) 1).val := by
    funext ⟨k, p₀⟩
    simp only [mapKernelOfMatrix, coordinates_symm_apply, NovikovSeries.coeff_mul_single, mul_one]
  rw [h]
  exact Subtype.property _

include hF₀ in
/-- The matrix of the kernel of a matrix, relative to the same reference generators, is the
matrix itself: the output of the kernel at the reference generator of the orbit `i` has the row
`M i` as its coordinates. -/
@[simp]
theorem coordinates_mapKernelOfMatrix [Finite ι₀] (M : Matrix ι₁ ι₀ (NovikovSeries R H N))
    (i : ι₁) (k : ι₀) :
    coordinates hF₀ r₀ ⟨mapKernelOfMatrix r₁ r₀ M ⟨i, r₁ i⟩, mapKernelOfMatrix_mem hF₀ r₁ r₀ M _⟩
      k = M i k := by
  ext h
  simp [coordinates_coeff]

include hF₀ in
/-- An invariant kernel is the kernel of its matrix: one-input kernels invariant under
translating the input together with the output are determined by their matrices. -/
theorem mapKernelOfMatrix_coordinates [Finite ι₀] {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
    (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)
    (hm : ∀ (g : H) i (p₁ : P₁ i) k (p₀ : P₀ k), m ⟨i, g +ᵥ p₁⟩ ⟨k, g +ᵥ p₀⟩ = m ⟨i, p₁⟩ ⟨k, p₀⟩) :
    mapKernelOfMatrix r₁ r₀ (Matrix.of fun i k => coordinates hF₀ r₀ ⟨m ⟨i, r₁ i⟩, hmfin _⟩ k) =
      m := by
  funext ⟨i, p₁⟩ ⟨k, p₀⟩
  have e := hm (p₁ -ᵥ r₁ i) i (r₁ i) k (-(p₁ -ᵥ r₁ i) +ᵥ p₀)
  rw [vsub_vadd, vadd_neg_vadd] at e
  simp only [mapKernelOfMatrix_apply, Matrix.of_apply, coordinates_coeff, sub_eq_neg_add, add_vadd,
    vsub_vadd]
  exact e.symm

end Semiring

include hF₁ hF₀ in
/-- **The potential bound of the kernel of a matrix.** If the `(i, k)` entry of the matrix lies
in the period filtration at level `F₀(r₀ k) - F₁(r₁ i) - C`, then the kernel obeys the potential
bound with constant `C`. -/
theorem potential_le_of_mapKernelOfMatrix_ne_zero [AddGroup R]
    {M : Matrix ι₁ ι₀ (NovikovSeries R H N)} {C : ℝ}
    (hM : ∀ i k, M i k ∈ NovikovSeries.periodFiltration R N (F₀ ⟨k, r₀ k⟩ - F₁ ⟨i, r₁ i⟩ - C))
    (p₁ : Σ i, P₁ i) (p₀ : Σ k, P₀ k) (h : mapKernelOfMatrix r₁ r₀ M p₁ p₀ ≠ 0) :
    F₀ p₀ ≤ F₁ p₁ + C := by
  obtain ⟨i, p₁⟩ := p₁
  obtain ⟨k, p₀⟩ := p₀
  have hN := not_lt.1 fun hlt => h (NovikovSeries.mem_periodFiltration.1 (hM i k) _ hlt)
  rw [map_sub] at hN
  rw [potential_eq_sub_vsub hF₁ r₁ i p₁, potential_eq_sub_vsub hF₀ r₀ k p₀]
  linarith

section Map

variable [CommSemiring R] [Finite ι₁] [Finite ι₀] (M : Matrix ι₁ ι₀ (NovikovSeries R H N))

/-- **The Novikov-linear map of a matrix of Novikov series.** For finitely many orbits and
reference generators `r₁` and `r₀`, every matrix `M` of Novikov series defines the map of its
kernel `NovikovModule.mapKernelOfMatrix`, a linear map over the Novikov ring for the module
structures of `TauCeti.NovikovModule.module`. In the reference coordinates it is
`cₖ = ∑ᵢ aᵢ Mᵢₖ` (`NovikovModule.coordinates_novikovMapOfMatrix`). -/
def novikovMapOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₀ :=
  novikovKernelMap hF₁ hF₀
    (exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀ M).choose_spec
    (mapKernelOfMatrix_mem hF₀ r₁ r₀ M) (mapKernelOfMatrix_vadd r₁ r₀ M)

/-- The coefficient of a generator in the image under the map of a matrix is the finite sum,
over all input generators, of the product of their coefficients with the kernel of the matrix. -/
@[simp]
theorem novikovMapOfMatrix_apply_val (a : NovikovModule R F₁) (p₀ : Σ k, P₀ k) :
    (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M a).val p₀ =
      ∑ᶠ p₁, a.val p₁ * mapKernelOfMatrix r₁ r₀ M p₁ p₀ := by
  rw [novikovMapOfMatrix, novikovKernelMap_apply, kernelMap_apply_val]

/-- The map of a matrix is the kernel map of its kernel, for any potential bound of that kernel.
Thus the results on kernel maps, such as the shift of potential cutoffs by `C`, apply to it. -/
theorem novikovMapOfMatrix_eq_kernelMap {C : ℝ}
    (hm : ∀ p₁ p₀, mapKernelOfMatrix r₁ r₀ M p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
    (a : NovikovModule R F₁) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M a = kernelMap hm (mapKernelOfMatrix_mem hF₀ r₁ r₀ M) a := by
  ext p₀
  rw [novikovMapOfMatrix_apply_val, kernelMap_apply_val]

/-- **The matrix formula for the map of a matrix.** In the coordinates relative to the reference
generators, the image of `a` is `cₖ = ∑ᵢ aᵢ Mᵢₖ`. -/
theorem coordinates_novikovMapOfMatrix [Fintype ι₁] (a : NovikovModule R F₁) (k : ι₀) :
    coordinates hF₀ r₀ (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M a) k =
      ∑ i, coordinates hF₁ r₁ a i * M i k := by
  rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ M
      (exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀ M).choose_spec,
    coordinates_kernelMap hF₁ hF₀ _ _ (mapKernelOfMatrix_vadd r₁ r₀ M) r₁ r₀]
  simp only [coordinates_mapKernelOfMatrix]

/-- **The map of a matrix is Mathlib's linear map of its transpose.** Relative to the reference
bases, the map of `M` sends `eᵢ` to `∑ₖ Mᵢₖ eₖ`, so it is `Matrix.toLin` of the transpose `Mᵀ`.
Results on `Matrix.toLin`, such as `Matrix.toLin_toMatrix`, apply to it through this
identification. -/
theorem novikovMapOfMatrix_eq_toLin [Fintype ι₁] [DecidableEq ι₁] :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M =
      Matrix.toLin (basis hF₁ r₁) (basis hF₀ r₀) (Matrix.transpose M) := by
  classical
  let := module (R := R) hF₁
  let := module (R := R) hF₀
  have := Fintype.ofFinite ι₀
  refine (basis hF₁ r₁).ext fun i => (basis hF₀ r₀).repr.injective (Finsupp.ext fun k => ?_)
  simp [coordinates_novikovMapOfMatrix, Matrix.toLin_self, Pi.single_apply, Finsupp.single_apply]

/-- The map of the zero matrix is zero. -/
@[simp]
theorem novikovMapOfMatrix_zero :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (0 : Matrix ι₁ ι₀ (NovikovSeries R H N)) = 0 := by
  classical
  have := Fintype.ofFinite ι₁
  rw [novikovMapOfMatrix_eq_toLin, Matrix.transpose_zero, map_zero]

/-- The map of a sum of matrices is the sum of their maps. -/
theorem novikovMapOfMatrix_add (A B : Matrix ι₁ ι₀ (NovikovSeries R H N)) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (A + B) =
      novikovMapOfMatrix hF₁ hF₀ r₁ r₀ A + novikovMapOfMatrix hF₁ hF₀ r₁ r₀ B := by
  classical
  have := Fintype.ofFinite ι₁
  simp only [novikovMapOfMatrix_eq_toLin, Matrix.transpose_add, map_add]

/-- The map of a Novikov multiple of a matrix is the same multiple of its map. -/
theorem novikovMapOfMatrix_smul (c : NovikovSeries R H N)
    (A : Matrix ι₁ ι₀ (NovikovSeries R H N)) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (c • A) = c • novikovMapOfMatrix hF₁ hF₀ r₁ r₀ A := by
  classical
  have := Fintype.ofFinite ι₁
  simp only [novikovMapOfMatrix_eq_toLin, Matrix.transpose_smul, map_smul]

/-- **Matrix multiplication is composition.** The map of the matrix product `A * B` is the
composite of the maps of `A` and `B`. -/
theorem novikovMapOfMatrix_mul [Fintype ι₀] [Finite ι₂] (A : Matrix ι₁ ι₀ (NovikovSeries R H N))
    (B : Matrix ι₀ ι₂ (NovikovSeries R H N)) :
    novikovMapOfMatrix hF₁ hF₂ r₁ r₂ (A * B) =
      (novikovMapOfMatrix hF₀ hF₂ r₀ r₂ B).comp (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ A) := by
  have := Fintype.ofFinite ι₁
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  refine LinearMap.ext fun a => (coordinates hF₂ r₂).injective (funext fun l => ?_)
  simp only [LinearMap.comp_apply, coordinates_novikovMapOfMatrix, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The identity matrix gives the identity map. -/
@[simp]
theorem novikovMapOfMatrix_one [DecidableEq ι₁] :
    letI := module (R := R) hF₁
    novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (1 : Matrix ι₁ ι₁ (NovikovSeries R H N)) = LinearMap.id := by
  have := Fintype.ofFinite ι₁
  let := module (R := R) hF₁
  rw [novikovMapOfMatrix_eq_toLin, Matrix.transpose_one, Matrix.toLin_one]

end Map

end TauCeti.NovikovModule

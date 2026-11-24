/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.GradedMatrix
public import TauCeti.RingTheory.NovikovModule.MapOfMatrix
public import TauCeti.RingTheory.NovikovModule.Specialization
public import TauCeti.RingTheory.NovikovModule.Tensor.Basic

/-!
# Laurent extensions of matrices and their cyclic specialization

Let `D : Matrix ι₁ ι₀ R` be a matrix over a ring and `H` a group of periods. The generators
`⟨i, g⟩` of `Σ _ : ι₁, H` are the generators of `ι₁` tensored with the period monomials `e^g`.
The *Laurent extension* of `D` (`TauCeti.NovikovModule.laurentKernelOfMatrix`) is the kernel
sending `⟨i, g⟩` to `∑ₖ D i k • ⟨k, g⟩`: the matrix `D ⊗ 1` on `R^{ι₁} ⊗ R[H]`, the tensor product
`TauCeti.NovikovModule.kernelTensor` of `D` with the identity kernel
(`TauCeti.NovikovModule.laurentKernelOfMatrix_apply_eq_kernelTensor`). It is the kernel of the
matrix of constant Novikov series `D i k • e^0`
(`TauCeti.NovikovModule.laurentKernelOfMatrix_eq_mapKernelOfMatrix`), it is invariant under the
periods, products of matrices give composites of kernels
(`TauCeti.NovikovModule.kernelComp_laurentKernelOfMatrix`), and its specialization `t ↦ 1` is `D`
itself (`TauCeti.NovikovModule.cyclicMatrix_laurentKernelOfMatrix`).

Let `D` be square with integer degrees `e : ι → ℤ` on the generators, raising them by one, with
`D * D = 0`, so that `K = gradedMatrixComplex e D` is a bounded integer-graded complex. For a
degree on the generators `⟨i, g⟩` reading `e i` modulo `n`, for instance the Laurent degree
`e i + c g` modulo `n` for a homomorphism `c : H →+ ℤ` with values in `nℤ`
(`TauCeti.NovikovModule.intCast_add_eq_of_dvd`), the Laurent extension is a Laurent differential,
and its cyclic complex is the complex of `D` with the degrees read modulo `n`
(`TauCeti.NovikovModule.cyclicComplexLaurentKernelOfMatrixIso`), that is, the `n`-periodic
compression of `K`. So its homology in residue `r` is the direct sum of the homology of `K` in the
degrees congruent to `r` (`TauCeti.NovikovModule.homologyCyclicComplexLaurentKernelOfMatrixIso`).

In capped Hamiltonian Floer theory on a positively monotone target, `K` is a Morse complex graded
by the shifted Morse index, `H` is the period group, `c` is twice the first Chern number and `n` is
twice the minimal Chern number. The Laurent extension of the Morse differential is the finite
Laurent Morse complex `M ⊗_R R[Γ]`, the target of the PSS comparison. Through a Laurent homotopy
equivalence with it, the cyclic Floer complex of a nondegenerate Hamiltonian, graded modulo `2N`,
has homology `HF^cyc_r ≅ ⨁_{j ≡ r} H^j(K)`
(`TauCeti.NovikovModule.homologyCyclicComplexIsoOfLaurentEquiv`), and over a field its number of
generators, the number of contractible periodic orbits, is at least the total dimension of the
homology of `K` (`TauCeti.NovikovModule.sum_finrank_homology_le_card_of_laurentEquiv`), which is
the total Betti number when `K` computes the homology of the manifold.

## Main definitions

* `TauCeti.NovikovModule.laurentKernelOfMatrix`: the Laurent extension of a matrix.
* `TauCeti.NovikovModule.cyclicComplexLaurentKernelOfMatrixIso`: the cyclic complex of the Laurent
  extension of a graded matrix is the complex of the matrix with the degrees read modulo `n`.

## Main results

* `TauCeti.NovikovModule.homologyCyclicComplexLaurentKernelOfMatrixIso`: its homology in residue
  `r` is `⨁_{j ≡ r} H^j(gradedMatrixComplex e D)`.
* `TauCeti.NovikovModule.homologyCyclicComplexIsoOfLaurentEquiv`: so is the homology of the cyclic
  complex of a Laurent differential homotopy equivalent to the Laurent extension.
* `TauCeti.NovikovModule.sum_finrank_homology_le_card_of_laurentEquiv`: over a field, the number
  of orbits of such a Laurent differential is at least the total dimension of `H^*(K)`.

## References

* S. Piunikhin, D. Salamon, M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open CategoryTheory Limits Module Function

namespace TauCeti

namespace NovikovModule

section LaurentKernelOfMatrix

variable {R H ι₁ ι₀ ι₂ : Type*} [DecidableEq H]

/-- The *Laurent extension* of a matrix `M`: the kernel from `Σ _ : ι₁, H` to `Σ _ : ι₀, H`
sending the generator `⟨i, g⟩` to `∑ₖ M i k • ⟨k, g⟩`, the matrix `M ⊗ 1` on generators tensored
with period monomials. -/
def laurentKernelOfMatrix [Zero R] (M : Matrix ι₁ ι₀ R) : (Σ _ : ι₁, H) → (Σ _ : ι₀, H) → R :=
  fun p q ↦ if p.snd = q.snd then M p.fst q.fst else 0

@[simp]
theorem laurentKernelOfMatrix_apply [Zero R] (M : Matrix ι₁ ι₀ R) (i : ι₁) (g : H) (k : ι₀)
    (h : H) :
    laurentKernelOfMatrix M ⟨i, g⟩ ⟨k, h⟩ = if g = h then M i k else 0 :=
  (rfl)

@[simp]
theorem laurentKernelOfMatrix_zero [Zero R] :
    laurentKernelOfMatrix (H := H) (0 : Matrix ι₁ ι₀ R) = 0 := by
  ext ⟨i, g⟩ ⟨k, h⟩
  simp

/-- The Laurent extension of the identity matrix is the identity kernel. -/
@[simp]
theorem laurentKernelOfMatrix_one [DecidableEq ι₁] [Zero R] [One R] :
    laurentKernelOfMatrix (H := H) (1 : Matrix ι₁ ι₁ R) = fun p q ↦ if p = q then 1 else 0 := by
  ext ⟨i, g⟩ ⟨k, h⟩
  by_cases hik : i = k <;> by_cases hgh : g = h <;> simp [hik, hgh]

/-- The Laurent extension is invariant under translating input and output by the same period. -/
theorem laurentKernelOfMatrix_vadd_vadd [AddGroup H] [Zero R] (M : Matrix ι₁ ι₀ R) (g : H) (i : ι₁)
    (p : H) (k : ι₀) (q : H) :
    laurentKernelOfMatrix M ⟨i, g +ᵥ p⟩ ⟨k, g +ᵥ q⟩ = laurentKernelOfMatrix M ⟨i, p⟩ ⟨k, q⟩ := by
  simp

/-- The outputs of the Laurent extension of a matrix with finitely many columns are finite
combinations. -/
theorem finite_support_laurentKernelOfMatrix [Zero R] [Finite ι₀] (M : Matrix ι₁ ι₀ R)
    (p : Σ _ : ι₁, H) : (support (laurentKernelOfMatrix M p)).Finite :=
  (Set.finite_range fun k : ι₀ ↦ (⟨k, p.snd⟩ : Σ _ : ι₀, H)).subset fun ⟨k, h⟩ hq ↦ by
    obtain ⟨i, g⟩ := p
    by_cases hgh : g = h
    · exact ⟨k, by rw [hgh]⟩
    · simp [hgh] at hq

/-- The Laurent extension of a matrix is the tensor product of `M` with the identity kernel of the
periods, read on `Σ _ : ι, H ≃ ι × H`. -/
theorem laurentKernelOfMatrix_apply_eq_kernelTensor [Semiring R] (M : Matrix ι₁ ι₀ R)
    (p : Σ _ : ι₁, H) (q : Σ _ : ι₀, H) :
    laurentKernelOfMatrix M p q =
      kernelTensor (fun i k ↦ M i k) (fun g h : H ↦ if g = h then (1 : R) else 0)
        (p.fst, p.snd) (q.fst, q.snd) := by
  obtain ⟨i, g⟩ := p
  obtain ⟨k, h⟩ := q
  simp [kernelTensor_apply]

/-- The Laurent extension of a matrix is the kernel of the matrix of constant Novikov series
`M i k • e^0`, relative to the reference generators `0`. -/
theorem laurentKernelOfMatrix_eq_mapKernelOfMatrix {H : Type*} [AddCommGroup H] [DecidableEq H]
    {N : H →+ ℝ} [Zero R] (M : Matrix ι₁ ι₀ R) :
    laurentKernelOfMatrix M = mapKernelOfMatrix (P₁ := fun _ ↦ H) (P₀ := fun _ ↦ H) (fun _ ↦ 0)
      (fun _ ↦ 0) (Matrix.of fun i k ↦ (NovikovSeries.single 0 (M i k) : NovikovSeries R H N)) := by
  ext ⟨i, g⟩ ⟨k, h⟩
  rw [laurentKernelOfMatrix_apply, mapKernelOfMatrix_apply, Matrix.of_apply,
    NovikovSeries.coeff_single]
  simp [Pi.single_apply, sub_eq_zero, eq_comm]

/-- The Laurent extension of a matrix is a Laurent kernel of degree `c` if every nonzero entry
`M i k` raises the degree of each generator `⟨i, g⟩` to that of `⟨k, g⟩` by `c`. -/
theorem isLaurentKernel_laurentKernelOfMatrix [AddGroup H] [Zero R] [Finite ι₀] {A : Type*} [Add A]
    {d₁ : (Σ _ : ι₁, H) → A} {d₀ : (Σ _ : ι₀, H) → A} {c : A} {M : Matrix ι₁ ι₀ R}
    (hM : ∀ i k g, M i k ≠ 0 → d₀ ⟨k, g⟩ = d₁ ⟨i, g⟩ + c) :
    IsLaurentKernel (H := H) d₁ d₀ c (laurentKernelOfMatrix M) where
  apply_vadd_vadd := laurentKernelOfMatrix_vadd_vadd M
  finite_support := finite_support_laurentKernelOfMatrix M
  degree_eq := fun ⟨i, g⟩ ⟨k, h⟩ hm ↦ by
    by_cases hgh : g = h
    · subst hgh
      exact hM i k g fun h ↦ hm (by simp [h])
    · simp [hgh] at hm

/-- **The composite of the Laurent extensions of two matrices is the Laurent extension of their
product.** -/
@[simp]
theorem kernelComp_laurentKernelOfMatrix [Semiring R] [Fintype ι₀] (M : Matrix ι₁ ι₀ R)
    (M' : Matrix ι₀ ι₂ R) :
    kernelComp (laurentKernelOfMatrix (H := H) M) (laurentKernelOfMatrix M') =
      laurentKernelOfMatrix (M * M') := by
  ext ⟨i, g⟩ ⟨k, h⟩
  have hfin : (support fun r : Σ _ : ι₀, H ↦
      laurentKernelOfMatrix M ⟨i, g⟩ r * laurentKernelOfMatrix M' r ⟨k, h⟩).Finite :=
    (finite_support_laurentKernelOfMatrix M ⟨i, g⟩).subset (support_mul_subset_left _ _)
  have hl (l : ι₀) : ∑ᶠ h' : H,
      laurentKernelOfMatrix M ⟨i, g⟩ ⟨l, h'⟩ * laurentKernelOfMatrix M' ⟨l, h'⟩ ⟨k, h⟩ =
      if g = h then M i l * M' l k else 0 := by
    rw [finsum_eq_single _ g fun g' hg' ↦ by simp [Ne.symm hg']]
    by_cases hgh : g = h <;> simp [hgh]
  rw [kernelComp_apply, finsum_sigma (M := R) _ hfin, finsum_eq_sum_of_fintype (M := R)]
  simp only [hl]
  by_cases hgh : g = h <;> simp [hgh, Matrix.mul_apply]

/-- **The cyclic specialization of the Laurent extension of a matrix is the matrix.** -/
@[simp]
theorem cyclicMatrix_laurentKernelOfMatrix [AddGroup H] [AddCommMonoid R] (M : Matrix ι₁ ι₀ R) :
    cyclicMatrix (laurentKernelOfMatrix (H := H) M) = M := by
  ext i k
  rw [cyclicMatrix_apply (laurentKernelOfMatrix_vadd_vadd M) (0 : H), orbitSum_apply,
    finsum_eq_single _ 0 fun h hh ↦ by simp [Ne.symm hh]]
  simp

end LaurentKernelOfMatrix

section CyclicComplex

universe u v

variable {R : Type u} [CommRing R] {H : Type*} {ι : Type v} {n : ℕ} {e : ι → ℤ}
  {D : Matrix ι ι R} (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1)
  {d : (Σ _ : ι, H) → ZMod n} (hd : ∀ p, d p = e p.fst)

/-- The Laurent degree `e i + c g` of the generator `⟨i, g⟩`, for a homomorphism `c` with values
in `nℤ`, reads `e i` modulo `n`. -/
theorem intCast_add_eq_of_dvd [AddGroup H] {c : H →+ ℤ} (hc : ∀ g, (n : ℤ) ∣ c g)
    (p : Σ _ : ι, H) : ((e p.fst + c p.snd : ℤ) : ZMod n) = e p.fst := by
  rw [Int.cast_add, (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (hc _), add_zero]

include hd in
/-- A degree reading `e` modulo `n` is invariant under the periods. -/
theorem apply_vadd_of_intCast [AddGroup H] (i : ι) (g p : H) : d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩ := by
  rw [hd, hd]

include hd in
/-- The orbit degree of a degree reading `e` modulo `n` is `e` modulo `n`. -/
theorem orbitDegree_eq_intCast [AddGroup H] (i : ι) : orbitDegree d i = e i := by
  rw [orbitDegree_apply (apply_vadd_of_intCast hd) (0 : H), hd]

include hd hD in
/-- The Laurent extension of a graded matrix raising degrees by one is a Laurent differential for a
degree reading `e` modulo `n`. -/
theorem isLaurentKernel_laurentKernelOfMatrix_of_intCast [AddGroup H] [DecidableEq H] [Finite ι] :
    IsLaurentKernel (H := H) d d 1 (laurentKernelOfMatrix D) :=
  isLaurentKernel_laurentKernelOfMatrix fun i k g h ↦ by
    rw [hd, hd, gradedMatrix_degree_intCast hD i k h]

variable [AddGroup H] [DecidableEq H] [Fintype ι] (hDD : D * D = 0)

omit [AddGroup H] in
include hDD in
/-- The Laurent extension of a matrix squaring to zero squares to zero. -/
theorem kernelComp_laurentKernelOfMatrix_self_eq_zero (p q : Σ _ : ι, H) :
    kernelComp (laurentKernelOfMatrix D) (laurentKernelOfMatrix D) p q = 0 := by
  rw [kernelComp_laurentKernelOfMatrix, hDD, laurentKernelOfMatrix_zero, Pi.zero_apply,
    Pi.zero_apply]

/-- The basis of the cyclic complex of the Laurent extension of `D` by the orbits, indexed by the
generators whose degree is congruent to the residue. -/
private def cyclicBasis (r : ZMod n) :
    Module.Basis {i // (e i : ZMod n) = r} R
      ((cyclicComplex R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
        (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
        (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD)).X r) :=
  (cyclicComplexBasis R d _ _ _ _ r).reindex
    (Equiv.subtypeEquivRight fun i ↦ by rw [orbitDegree_eq_intCast hd])

private theorem cyclicBasis_d (r s : ZMod n) (i : {i // (e i : ZMod n) = r}) :
    ((cyclicComplex R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
        (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
        (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD)).d r s).hom
          (cyclicBasis hD hd hDD r i) =
      ∑ k : {k // (e k : ZMod n) = s}, D i k • cyclicBasis hD hd hDD s k := by
  rw [cyclicBasis, Basis.reindex_apply, cyclicComplex_d_basis, cyclicMatrix_laurentKernelOfMatrix]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun k ↦ by
    rw [orbitDegree_eq_intCast hd]) _ _ fun k ↦ by simp [cyclicBasis, Basis.reindex_apply]

variable (R) in
/-- **The cyclic complex of the Laurent extension of a graded matrix** is the complex of the
matrix with the degrees read modulo `n`, the `n`-periodic compression of `gradedMatrixComplex e D`
(`TauCeti.PeriodicComplex.compressionGradedMatrixComplexIso`). The orbit of a generator goes to the
generator (`TauCeti.NovikovModule.cyclicComplexLaurentKernelOfMatrixIso_hom_f_basis`). -/
def cyclicComplexLaurentKernelOfMatrixIso :
    cyclicComplex R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
        (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
        (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD) ≅
      gradedMatrixComplex (fun i ↦ (e i : ZMod n)) D
        (gradedMatrix_degree_intCast hD) hDD :=
  isoGradedMatrixComplexOfBasis _ _ _ _ (cyclicBasis hD hd hDD) (cyclicBasis_d hD hd hDD)

/-- The isomorphism `cyclicComplexLaurentKernelOfMatrixIso` sends the orbit of a generator to the
generator. -/
@[simp]
theorem cyclicComplexLaurentKernelOfMatrixIso_hom_f_basis (r : ZMod n)
    (i : {i // orbitDegree d i = r}) :
    ((cyclicComplexLaurentKernelOfMatrixIso R hD hd hDD).hom.f r).hom
        (cyclicComplexBasis R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
          (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
          (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD) r i) =
      gradedMatrixComplexBasis _ D (gradedMatrix_degree_intCast hD) hDD
        r ⟨i, (orbitDegree_eq_intCast hd i).symm.trans i.property⟩ := by
  have h := isoGradedMatrixComplexOfBasis_hom_f_basis
    (hD := gradedMatrix_degree_intCast hD) (hDD := hDD)
    (cyclicBasis hD hd hDD)
    (cyclicBasis_d hD hd hDD) r ⟨i, (orbitDegree_eq_intCast hd i).symm.trans i.property⟩
  rwa [cyclicBasis, Basis.reindex_apply, Equiv.subtypeEquivRight_symm_apply] at h

/-- The inverse of `cyclicComplexLaurentKernelOfMatrixIso` sends a generator to its orbit. -/
@[simp]
theorem cyclicComplexLaurentKernelOfMatrixIso_inv_f_basis (r : ZMod n)
    (i : {i // (e i : ZMod n) = r}) :
    ((cyclicComplexLaurentKernelOfMatrixIso R hD hd hDD).inv.f r).hom
        (gradedMatrixComplexBasis _ D (gradedMatrix_degree_intCast hD) hDD r i) =
      cyclicComplexBasis R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
        (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
        (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD) r
        ⟨i, (orbitDegree_eq_intCast hd i).trans i.property⟩ := by
  have h := isoGradedMatrixComplexOfBasis_inv_f_basis
    (hD := gradedMatrix_degree_intCast hD) (hDD := hDD)
    (cyclicBasis hD hd hDD) (cyclicBasis_d hD hd hDD) r i
  rwa [cyclicBasis, Basis.reindex_apply, Equiv.subtypeEquivRight_symm_apply] at h

/-- **The homology of the cyclic complex of the Laurent extension of a graded matrix.** If the
degrees of the generators lie in `[a, b]`, its homology in residue `r` is the direct sum of the
homology of `gradedMatrixComplex e D` in the degrees of `[a, b]` congruent to `r`. -/
def homologyCyclicComplexLaurentKernelOfMatrixIso (a b : ℤ) (ha : ∀ i, a ≤ e i) (hb : ∀ i, e i ≤ b)
    (r : ZMod n) :
    (cyclicComplex R d (apply_vadd_of_intCast hd) (laurentKernelOfMatrix D)
        (isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
        (kernelComp_laurentKernelOfMatrix_self_eq_zero hDD)).homology r ≅
      ⨁ fun j : ({j ∈ Finset.Icc a b | (j : ZMod n) = r} : Finset ℤ) ↦
        (gradedMatrixComplex e D hD hDD).homology j :=
  (HomologicalComplex.homologyFunctor _ _ r).mapIso
      (cyclicComplexLaurentKernelOfMatrixIso R hD hd hDD) ≪≫
    PeriodicComplex.homologyGradedMatrixComplexIntCastIso n e D hD hDD a b ha hb r

end CyclicComplex

section LaurentEquiv

universe u v

variable {R : Type u} [CommRing R] {H : Type*} [AddGroup H] [DecidableEq H] {ι₁ ι : Type v}
  [Fintype ι₁] [Fintype ι] [DecidableEq ι₁] [DecidableEq ι] {P₁ : ι₁ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [DecidableEq (Σ i, P₁ i)] {n : ℕ} {e : ι → ℤ} {D : Matrix ι ι R}
  (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1) (hDD : D * D = 0) {d : (Σ _ : ι, H) → ZMod n}
  (hd : ∀ p, d p = e p.fst) {d₁ : (Σ i, P₁ i) → ZMod n}
  (hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩)
  {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} (hδ₁ : IsLaurentKernel d₁ d₁ 1 δ₁)
  (hδδ₁ : ∀ p q, kernelComp δ₁ δ₁ p q = 0) {Φ : (Σ i, P₁ i) → (Σ _ : ι, H) → R}
  {Ψ : (Σ _ : ι, H) → (Σ i, P₁ i) → R} {K : (Σ i, P₁ i) → (Σ i, P₁ i) → R}
  {K' : (Σ _ : ι, H) → (Σ _ : ι, H) → R} (hΦ : IsLaurentKernel d₁ d 0 Φ)
  (hΨ : IsLaurentKernel d d₁ 0 Ψ) (hK : IsLaurentKernel d₁ d₁ (-1) K)
  (hK' : IsLaurentKernel d d (-1) K')
  (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ (laurentKernelOfMatrix D) p q)
  (hΨδ : ∀ p q, kernelComp (laurentKernelOfMatrix D) Ψ p q = kernelComp Ψ δ₁ p q)
  (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
    kernelComp K δ₁ p q + kernelComp δ₁ K p q)
  (hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
    kernelComp K' (laurentKernelOfMatrix D) p q + kernelComp (laurentKernelOfMatrix D) K' p q)

/-- **The cyclic homology of a Laurent differential equivalent to the Laurent extension of a
graded matrix.** Let `δ₁` be a Laurent differential, with Laurent chain maps `Φ` and `Ψ` of degree
`0` to and from the Laurent extension of `D`, inverse to each other up to Laurent homotopies `K`
and `K'` of degree `-1`. If the degrees of the generators of `D` lie in `[a, b]`, the homology of
the cyclic complex of `δ₁` in residue `r` is the direct sum of the homology of
`gradedMatrixComplex e D` in the degrees of `[a, b]` congruent to `r`:
`HF^cyc_r ≅ ⨁_{j ≡ r} H^j(gradedMatrixComplex e D)`. -/
def homologyCyclicComplexIsoOfLaurentEquiv (a b : ℤ) (ha : ∀ i, a ≤ e i) (hb : ∀ i, e i ≤ b)
    (r : ZMod n) :
    (cyclicComplex R d₁ hd₁ δ₁ hδ₁ hδδ₁).homology r ≅
      ⨁ fun j : ({j ∈ Finset.Icc a b | (j : ZMod n) = r} : Finset ℤ) ↦
        (gradedMatrixComplex e D hD hDD).homology j :=
  (cyclicComplexHomotopyEquiv (hd₀ := apply_vadd_of_intCast hd)
      (hδ₀ := isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
      (hδδ₀ := kernelComp_laurentKernelOfMatrix_self_eq_zero hDD) Φ Ψ K K' hΦ hΨ hK hK' hΦδ hΨδ hΦΨ
      hΨΦ).toHomologyIso r ≪≫
    homologyCyclicComplexLaurentKernelOfMatrixIso hD hd hDD a b ha hb r

end LaurentEquiv

section Finrank

universe u v

variable {𝕜 : Type u} [Field 𝕜] {H : Type*} [AddGroup H] [DecidableEq H] {ι₁ ι : Type v}
  [Fintype ι₁] [Fintype ι] [DecidableEq ι] {P₁ : ι₁ → Type*} [∀ i, AddTorsor H (P₁ i)]
  [DecidableEq (Σ i, P₁ i)] {n : ℕ} [NeZero n] {e : ι → ℤ} {D : Matrix ι ι 𝕜}
  (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1) (hDD : D * D = 0) {d : (Σ _ : ι, H) → ZMod n}
  (hd : ∀ p, d p = e p.fst) {d₁ : (Σ i, P₁ i) → ZMod n}
  {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → 𝕜} {Φ : (Σ i, P₁ i) → (Σ _ : ι, H) → 𝕜}
  {Ψ : (Σ _ : ι, H) → (Σ i, P₁ i) → 𝕜} {K : (Σ i, P₁ i) → (Σ i, P₁ i) → 𝕜}
  {K' : (Σ _ : ι, H) → (Σ _ : ι, H) → 𝕜}

include hd in
/-- **Counting orbits by the homology of a graded matrix.** Over a field, let `δ₁` be a Laurent
differential with Laurent chain maps `Φ` and `Ψ` of degree `0` to and from the Laurent extension
of a graded matrix `D`, inverse to each other up to Laurent homotopies of degree `-1`, with degrees
modulo a positive `n`. If the degrees of the generators of `D` lie in `[a, b]`, the number of
orbits of generators of `δ₁` is at least the total dimension of the homology of
`gradedMatrixComplex e D`. -/
theorem sum_finrank_homology_le_card_of_laurentEquiv (a b : ℤ) (ha : ∀ i, a ≤ e i)
    (hb : ∀ i, e i ≤ b) (hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩)
    (hδ₁ : IsLaurentKernel d₁ d₁ 1 δ₁) (hδδ₁ : ∀ p q, kernelComp δ₁ δ₁ p q = 0)
    (hΦ : IsLaurentKernel d₁ d 0 Φ) (hΨ : IsLaurentKernel d d₁ 0 Ψ)
    (hK : IsLaurentKernel d₁ d₁ (-1) K) (hK' : IsLaurentKernel d d (-1) K')
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ (laurentKernelOfMatrix D) p q)
    (hΨδ : ∀ p q, kernelComp (laurentKernelOfMatrix D) Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q)
    (hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
      kernelComp K' (laurentKernelOfMatrix D) p q + kernelComp (laurentKernelOfMatrix D) K' p q) :
    ∑ j ∈ Finset.Icc a b, finrank 𝕜 ((gradedMatrixComplex e D hD hDD).homology j) ≤
      Fintype.card ι₁ := by
  rw [← PeriodicComplex.sum_finrank_homology_gradedMatrixComplex_intCast n e D hD hDD a b ha hb]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun r _ ↦ ?_)
    (sum_finrank_homology_cyclicComplex_le_card hd₁ hδ₁ hδδ₁ Φ Ψ K K' hΦ hΨ hK hK' hΦδ hΨδ hΦΨ
      hΨΦ (hd₀ := apply_vadd_of_intCast hd)
      (hδ₀ := isLaurentKernel_laurentKernelOfMatrix_of_intCast hD hd)
      (hδδ₀ := kernelComp_laurentKernelOfMatrix_self_eq_zero hDD))
  exact ((HomologicalComplex.homologyFunctor _ _ r).mapIso
    (cyclicComplexLaurentKernelOfMatrixIso 𝕜 hD hd hDD)).toLinearEquiv.finrank_eq.symm

end Finrank

end NovikovModule

end TauCeti

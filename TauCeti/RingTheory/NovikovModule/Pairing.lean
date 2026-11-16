/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Pairings of completed combinations into the Novikov ring

Let `M₁ = NovikovModule R F₁` and `M₂ = NovikovModule R F₂` be completed combinations on finite
unions `Σ i, P₁ i` and `Σ i, P₂ i` of torsors under a commutative group `H`, indexed by the same
finite type `ι`, with equivariant potentials `F (h +ᵥ p) = F p - N h`, and fix reference generators
`r₁`, `r₂`. Each is a finite free module over the Novikov ring `Λ = NovikovSeries R H N`, with the
basis of reference generators (`TauCeti.NovikovModule.basis`).

A matrix `G : Matrix ι ι Λ` defines a product kernel from `M₁ × M₂` into the completed combinations
of the single orbit `Σ _ : Unit, H` with potential `⟨(), h⟩ ↦ -N h`, whose coordinate at the
reference generator `0` identifies them with `Λ`. Its coefficient on generators `p₁`, `p₂` in the
orbits `i`, `j` and on the output `⟨(), C⟩` is the coefficient of `G i j` at
`C - (p₁ -ᵥ r₁ i) - (p₂ -ᵥ r₂ j)`; for a constant entry `G i j = g` this is `g` when `C` is the sum
of the two displacements and `0` otherwise. The product of this kernel
(`TauCeti.NovikovModule.novikovProductOfMatrix`) read in that coordinate is the `Λ`-bilinear pairing
`TauCeti.NovikovModule.novikovPairingOfMatrix G : M₁ →ₗ[Λ] M₂ →ₗ[Λ] Λ`, given in reference
coordinates by `⟨a, b⟩ = ∑ᵢ ∑ⱼ aᵢ bⱼ Gᵢⱼ`.

* **Gram matrix.** The pairing of the reference basis vectors `i` and `j` is `G i j`, so the Gram
  matrix of the pairing in the reference bases is `G`
  (`TauCeti.NovikovModule.toMatrix₂_novikovPairingOfMatrix`), and every `Λ`-bilinear pairing of
  `M₁` and `M₂` into `Λ` is the pairing of its Gram matrix
  (`TauCeti.NovikovModule.eq_novikovPairingOfMatrix`). Through the coordinates it is the bilinear
  form `(v, w) ↦ v ⬝ᵥ (G *ᵥ w)` of Mathlib's `Matrix.toLinearMap₂'`
  (`TauCeti.NovikovModule.novikovPairingOfMatrix_eq_compl₁₂`).
* **Perfectness.** For a commutative ring `R`, the pairing of `G` is perfect, that is, both maps
  `M₁ → Dual Λ M₂` and `M₂ → Dual Λ M₁` are bijective, exactly when `det G` is a unit of `Λ`
  (`TauCeti.NovikovModule.isPerfPair_novikovPairingOfMatrix_iff`). In particular the pairing of a
  constant Gram matrix `g : Matrix ι ι R` with unit determinant, such as the invertible rational
  Gram matrix of a perfect pairing of graded rational vector spaces in a basis, is perfect
  (`TauCeti.NovikovModule.isPerfPair_novikovPairingOfMatrix_map_algebraMap`).
* **Filtration shift and continuity.** If every entry `G i j` lies in the period filtration at level
  `c - F₁ (r₁ i) - F₂ (r₂ j)`, the pairing sends combinations vanishing above the potentials `D₁`
  and `D₂` to series vanishing below the period `c - D₁ - D₂`
  (`TauCeti.NovikovModule.novikovPairingOfMatrix_mem_periodFiltration`); for a constant Gram matrix
  and reference generators of potential `0` this holds with `c = 0`
  (`TauCeti.NovikovModule.novikovPairingOfMatrix_map_algebraMap_mem_periodFiltration`). The pairing
  is jointly continuous (`TauCeti.NovikovModule.continuous_novikovPairingOfMatrix`).
* **Degree.** For degrees `d₁`, `d₂` on the generators that are shifted by recapping through a
  homomorphism `δ : H →+ D`, if each entry `G i j` is homogeneous of degree
  `d₁ (r₁ i) + d₂ (r₂ j) - n`, then the pairing of homogeneous combinations of degrees `k` and `l`
  is homogeneous of degree `k + l - n` (`TauCeti.NovikovModule.novikovPairingOfMatrix_mem_gradeBy`).
  For a constant Gram matrix this asks that `g i j` vanish unless
  `d₁ (r₁ i) + d₂ (r₂ j) = n`, as for a pairing of graded vector spaces of degree `-n`
  (`TauCeti.NovikovModule.novikovPairingOfMatrix_map_algebraMap_mem_gradeBy`).

For the completed state module of a closed symplectic manifold `X`, the generators are
`Σ (b : B), H₂(X; ℤ)` for a homogeneous basis `B` of the rational cohomology, with potential
`⟨b, A⟩ ↦ -ω(A)`, degree `⟨b, A⟩ ↦ deg b + 2 c₁(A)` and reference generators `⟨b, 0⟩`, and the
Poincaré pairing has a constant invertible Gram matrix of degree `-dim_ℝ X`. Its extension to
the completed state module is then a perfect `Λ_ω`-bilinear pairing into the Novikov ring which
lowers the degree by `dim_ℝ X`; this is the duality through which the quantum product is defined
from three-point invariants.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 11.1,
  on the quantum cohomology ring and the extension of the Poincaré pairing to Novikov coefficients.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

section Pairing

variable {R H ι : Type*} [AddCommGroup H] {N : H →+ ℝ} [Fintype ι]
  {P₁ P₂ : ι → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ i, AddTorsor H (P₂ i)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ i, P₂ i) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₂ : ∀ i h (p : P₂ i), F₂ ⟨i, h +ᵥ p⟩ = F₂ ⟨i, p⟩ - N h)
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ i, P₂ i)

/-- The potential `⟨(), h⟩ ↦ -N h` of the single orbit `Σ _ : Unit, H` is equivariant. -/
private theorem neg_period_vadd (u : Unit) (h p : H) :
    -N (⟨u, h +ᵥ p⟩ : Σ _ : Unit, H).2 = -N (⟨u, p⟩ : Σ _ : Unit, H).2 - N h := by
  simp only [vadd_eq_add, map_add]
  ring

section CommSemiring

variable [CommSemiring R]

/-- **The Novikov pairing of a matrix.** For a matrix `G` of Novikov series indexed by the orbits
of two completed modules with reference generators `r₁` and `r₂`, this is the product of the kernel
of the matrix `(i, j, ()) ↦ G i j` (`TauCeti.NovikovModule.novikovProductOfMatrix`) into the
completed combinations of the single orbit `Σ _ : Unit, H` with potential `⟨(), h⟩ ↦ -N h`, read in
the coordinate at the reference generator `0`, which identifies them with the Novikov ring. It is
bilinear over the Novikov ring for the module structures of `TauCeti.NovikovModule.module`, and in
reference coordinates it is `⟨a, b⟩ = ∑ᵢ ∑ⱼ aᵢ bⱼ Gᵢⱼ`
(`TauCeti.NovikovModule.novikovPairingOfMatrix_apply`). -/
def novikovPairingOfMatrix (G : Matrix ι ι (NovikovSeries R H N)) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovSeries R H N :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₂
  letI := module (R := R) (F := fun q : (Σ _ : Unit, H) => -N q.2) neg_period_vadd
  (novikovProductOfMatrix hF₁ hF₂ (F₀ := fun q : (Σ _ : Unit, H) => -N q.2) neg_period_vadd
      r₁ r₂ (fun _ => (0 : H)) fun i j _ => G i j).compr₂
    ((LinearMap.proj ()).comp (coordinatesLinearEquiv (R := R)
      (F := fun q : (Σ _ : Unit, H) => -N q.2) neg_period_vadd fun _ => (0 : H)).toLinearMap)

/-- **The coordinate formula for the Novikov pairing of a matrix.** In the coordinates relative to
the reference generators, the pairing of `a` and `b` is `∑ᵢ ∑ⱼ aᵢ bⱼ Gᵢⱼ`. -/
theorem novikovPairingOfMatrix_apply (G : Matrix ι ι (NovikovSeries R H N))
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G a b =
      ∑ i, ∑ j, coordinates hF₁ r₁ a i * coordinates hF₂ r₂ b j * G i j := by
  simp only [novikovPairingOfMatrix, LinearMap.compr₂_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, coordinatesLinearEquiv_apply, LinearMap.proj_apply]
  exact coordinates_novikovProductOfMatrix hF₁ hF₂ (F₀ := fun q : (Σ _ : Unit, H) => -N q.2)
    neg_period_vadd r₁ r₂ (fun _ => (0 : H)) (fun i j _ => G i j) a b ()

/-- **The Novikov pairing of a matrix in coordinates.** Read through the coordinates relative to
the reference generators, the Novikov pairing of `G` is the bilinear form `(v, w) ↦ v ⬝ᵥ (G *ᵥ w)`
of the matrix `G` on the coordinate modules (`Matrix.toLinearMap₂'`). -/
theorem novikovPairingOfMatrix_eq_compl₁₂ [DecidableEq ι]
    (G : Matrix ι ι (NovikovSeries R H N)) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G =
      (Matrix.toLinearMap₂' (NovikovSeries R H N) G).compl₁₂
        (coordinatesLinearEquiv hF₁ r₁).toLinearMap
        (coordinatesLinearEquiv hF₂ r₂).toLinearMap := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  rw [novikovPairingOfMatrix_apply, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply']
  simp only [LinearEquiv.coe_coe, coordinatesLinearEquiv_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The pairing of the reference basis vectors of the orbits `i` and `j` is the entry `G i j`. -/
@[simp]
theorem novikovPairingOfMatrix_basis (G : Matrix ι ι (NovikovSeries R H N)) (i j : ι) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G (basis hF₁ r₁ i) (basis hF₂ r₂ j) = G i j := by
  classical
  simp [novikovPairingOfMatrix_apply, Pi.single_apply]

/-- **The Gram matrix of the Novikov pairing of a matrix** in the reference bases is the matrix
itself. -/
@[simp]
theorem toMatrix₂_novikovPairingOfMatrix [DecidableEq ι] (G : Matrix ι ι (NovikovSeries R H N)) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    LinearMap.toMatrix₂ (basis hF₁ r₁) (basis hF₂ r₂) (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G) =
      G := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  ext i j
  rw [LinearMap.toMatrix₂_apply, novikovPairingOfMatrix_basis]

/-- **Every pairing into the Novikov ring is the pairing of its Gram matrix.** A bilinear map over
the Novikov ring from two completed modules into the Novikov ring is the Novikov pairing of its
matrix of values on the reference basis vectors. -/
theorem eq_novikovPairingOfMatrix (B :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovSeries R H N) :
    B = novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ (fun i j => B (basis hF₁ r₁ i) (basis hF₂ r₂ j)) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  refine (basis hF₁ r₁).ext fun i => (basis hF₂ r₂).ext fun j => ?_
  exact (novikovPairingOfMatrix_basis hF₁ hF₂ r₁ r₂
    (fun i j => B (basis hF₁ r₁ i) (basis hF₂ r₂ j)) i j).symm

/-- The Novikov pairing is determined by its matrix: distinct matrices give distinct pairings. -/
theorem novikovPairingOfMatrix_injective :
    Function.Injective (novikovPairingOfMatrix (R := R) hF₁ hF₂ r₁ r₂) := by
  intro G G' h
  ext i j
  rw [← novikovPairingOfMatrix_basis hF₁ hF₂ r₁ r₂ G, h, novikovPairingOfMatrix_basis]

end CommSemiring

section CommRing

variable [CommRing R] [DecidableEq ι]

/-- **Perfectness of the Novikov pairing of a matrix.** The pairing of `G` is a perfect pairing of
the two completed modules over the Novikov ring exactly when the determinant of `G` is a unit of
the Novikov ring. -/
theorem isPerfPair_novikovPairingOfMatrix_iff (G : Matrix ι ι (NovikovSeries R H N)) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G).IsPerfPair ↔ IsUnit G.det := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  constructor
  · intro h
    simpa using (basis hF₁ r₁).isUnit_det_of_isPerfPair (basis hF₂ r₂) _ h
  · intro h
    exact (basis hF₁ r₁).isPerfPair_of_isUnit_det (basis hF₂ r₂) _ (by simpa using h)

/-- **The pairing of a constant invertible Gram matrix is perfect.** For a matrix `g` over the
coefficient ring whose determinant is a unit, the Novikov pairing of the matrix of constant series
`g i j` is a perfect pairing over the Novikov ring. Over a field, such as `ℚ`, the condition is
`det g ≠ 0`. -/
theorem isPerfPair_novikovPairingOfMatrix_map_algebraMap (g : Matrix ι ι R) (hg : IsUnit g.det) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂
      (g.map (algebraMap R (NovikovSeries R H N)))).IsPerfPair :=
  (isPerfPair_novikovPairingOfMatrix_iff hF₁ hF₂ r₁ r₂ _).2 <| by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hg.map _

end CommRing

section Filtration

variable [CommRing R]

/-- **The filtration shift of the Novikov pairing.** If every entry `G i j` lies in the period
filtration at level `c - F₁ (r₁ i) - F₂ (r₂ j)`, then the pairing sends combinations vanishing above
the potentials `D₁` and `D₂` to a Novikov series vanishing below the period `c - D₁ - D₂`. -/
theorem novikovPairingOfMatrix_mem_periodFiltration {G : Matrix ι ι (NovikovSeries R H N)}
    {c : ℝ}
    (hG : ∀ i j, G i j ∈ NovikovSeries.periodFiltration R N (c - F₁ ⟨i, r₁ i⟩ - F₂ ⟨j, r₂ j⟩))
    {D₁ D₂ : ℝ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ potentialFiltration R F₁ D₁) (hb : b ∈ potentialFiltration R F₂ D₂) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G a b ∈
      NovikovSeries.periodFiltration R N (c - D₁ - D₂) := by
  rw [mem_potentialFiltration_iff_coordinates hF₁ r₁] at ha
  rw [mem_potentialFiltration_iff_coordinates hF₂ r₂] at hb
  rw [novikovPairingOfMatrix_apply]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  have hm := NovikovSeries.mul_mem_periodFiltration
    (NovikovSeries.mul_mem_periodFiltration (ha i) (hb j)) (hG i j)
  convert hm using 2
  ring

/-- **The filtration shift of the pairing of a constant Gram matrix.** If `c` is at most the sum
of the potentials of any two reference generators, the Novikov pairing of the matrix of constant
series `g i j` sends combinations vanishing above the potentials `D₁` and `D₂` to a Novikov series
vanishing below the period `c - D₁ - D₂`. For reference generators of potential `0` this holds with
`c = 0`. -/
theorem novikovPairingOfMatrix_map_algebraMap_mem_periodFiltration (g : Matrix ι ι R) {c : ℝ}
    (hc : ∀ i j, c ≤ F₁ ⟨i, r₁ i⟩ + F₂ ⟨j, r₂ j⟩)
    {D₁ D₂ : ℝ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ potentialFiltration R F₁ D₁) (hb : b ∈ potentialFiltration R F₂ D₂) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ (g.map (algebraMap R (NovikovSeries R H N))) a b ∈
      NovikovSeries.periodFiltration R N (c - D₁ - D₂) := by
  refine novikovPairingOfMatrix_mem_periodFiltration hF₁ hF₂ r₁ r₂ (fun i j => ?_) ha hb
  rw [Matrix.map_apply, NovikovSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, NovikovSeries.single_mem_periodFiltration_iff, map_zero]
  exact Or.inr (by linarith [hc i j])

/-- **Continuity of the Novikov pairing.** The Novikov pairing of a matrix is jointly continuous
for the potential-cutoff topologies of the two completed modules and the period topology of the
Novikov ring. -/
@[fun_prop]
theorem continuous_novikovPairingOfMatrix (G : Matrix ι ι (NovikovSeries R H N)) :
    Continuous fun p : NovikovModule R F₁ × NovikovModule R F₂ =>
      novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G p.1 p.2 := by
  obtain ⟨C, hC⟩ := exists_potential_le_of_kernelOfMatrix_ne_zero hF₁ hF₂
    (F₀ := fun q : (Σ _ : Unit, H) => -N q.2) neg_period_vadd r₁ r₂ (fun _ => (0 : H))
    fun i j _ => G i j
  have hfin := kernelOfMatrix_mem (R := R) (F₀ := fun q : (Σ _ : Unit, H) => -N q.2)
    neg_period_vadd r₁ r₂ (fun _ => (0 : H)) fun i j _ => G i j
  have h : (fun p : NovikovModule R F₁ × NovikovModule R F₂ =>
      novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G p.1 p.2) = fun p =>
      coordinates (F := fun q : (Σ _ : Unit, H) => -N q.2) neg_period_vadd (fun _ => (0 : H))
        (kernelProduct hC hfin p.1 p.2) () := by
    funext p
    rw [← novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ neg_period_vadd r₁ r₂]
    simp only [novikovPairingOfMatrix, LinearMap.compr₂_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, coordinatesLinearEquiv_apply, LinearMap.proj_apply]
  rw [h]
  exact (continuous_apply ()).comp
    ((continuous_coordinates neg_period_vadd _).comp (continuous_kernelProduct hC hfin))

end Filtration

section Grading

variable [CommSemiring R] {D : Type*} [AddCommGroup D] (δ : H →+ D)
  {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ i, P₂ i) → D}
  (hd₁ : ∀ i h (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
  (hd₂ : ∀ i h (p : P₂ i), d₂ ⟨i, h +ᵥ p⟩ = δ h + d₂ ⟨i, p⟩)

include hd₁ hd₂ in
/-- **The degree of the Novikov pairing.** If every entry `G i j` is homogeneous of degree
`d₁ (r₁ i) + d₂ (r₂ j) - n`, then the pairing of homogeneous combinations of degrees `k` and `l` is
a homogeneous Novikov series of degree `k + l - n`: the pairing lowers the total degree by `n`. -/
theorem novikovPairingOfMatrix_mem_gradeBy {G : Matrix ι ι (NovikovSeries R H N)} {n : D}
    (hG : ∀ i j, G i j ∈ NovikovSeries.gradeBy R N δ (d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩ - n))
    {k l : D} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ d₁ k) (hb : b ∈ gradeBy R F₂ d₂ l) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G a b ∈ NovikovSeries.gradeBy R N δ (k + l - n) := by
  rw [mem_gradeBy_iff_coordinates hF₁ δ hd₁ r₁] at ha
  rw [mem_gradeBy_iff_coordinates hF₂ δ hd₂ r₂] at hb
  rw [novikovPairingOfMatrix_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have hm := SetLike.mul_mem_graded (SetLike.mul_mem_graded (ha i) (hb j)) (hG i j)
  convert hm using 2
  abel

include hd₁ hd₂ in
/-- **The degree of the pairing of a constant Gram matrix.** If the entry `g i j` vanishes unless
the reference degrees satisfy `d₁ (r₁ i) + d₂ (r₂ j) = n`, as for a pairing of graded modules of
degree `-n` in homogeneous bases, then the Novikov pairing of the matrix of constant series
`g i j` sends homogeneous combinations of degrees `k` and `l` to a homogeneous Novikov series of
degree `k + l - n`. -/
theorem novikovPairingOfMatrix_map_algebraMap_mem_gradeBy {g : Matrix ι ι R} {n : D}
    (hg : ∀ i j, g i j ≠ 0 → d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩ = n)
    {k l : D} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ d₁ k) (hb : b ∈ gradeBy R F₂ d₂ l) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ (g.map (algebraMap R (NovikovSeries R H N))) a b ∈
      NovikovSeries.gradeBy R N δ (k + l - n) := by
  refine novikovPairingOfMatrix_mem_gradeBy hF₁ hF₂ r₁ r₂ δ hd₁ hd₂ (fun i j => ?_) ha hb
  rw [Matrix.map_apply, NovikovSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hij : g i j = 0
  · rw [hij, NovikovSeries.single_zero]
    exact Submodule.zero_mem _
  · rw [hg i j hij, sub_self, ← map_zero δ]
    exact NovikovSeries.single_mem_gradeBy _ _ _

end Grading

end Pairing

end TauCeti.NovikovModule

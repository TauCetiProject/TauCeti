/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.CohomologyRing
public import TauCeti.Geometry.Symplectic.Floer.Cap.Unit
import TauCeti.Geometry.Symplectic.Floer.Grading

/-!
# The cohomology ring of class-indexed counts

Fix finitely many orbits with capped generators `P` and reference caps `r`, actions `F` and
gradings `μ` obeying the recapping laws, and let every count be recorded by a generating series
in a common class group `G` mapping to the period group by an area-preserving homomorphism `q`,
as in `TauCeti.Geometry.Symplectic.Floer.Cap.Product`. On the completed capped module, graded by
the cochain degree `n - μ`, take

* the differential `d`, the ground-ring linear map of the counts `D` of rigid Floer cylinders;
* the product `⋆`, the ground-ring bilinear map of the counts `Q` of rigid pairs of pants whose
  three ends all lie in this complex, as for the product of a fixed Hamiltonian;
* the unit `e`, the combination of the counts `E` of rigid PSS planes constrained by the
  fundamental cycle.

The files `Cap/Product.lean` and `Cap/Unit.lean` derive the laws of `⋆` up to coboundaries from
the identities given by the ends of one-dimensional moduli spaces, for products between possibly
different complexes. This file applies them to a single complex, with each homotopy only
required to exist as a family of counts of the right index:

* associativity, from the family of four-punctured spheres between the two broken triple products
  (`TauCeti.Floer.kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries`);
* graded commutativity, from the input-exchange family between `Q` and `Q` with its inputs
  exchanged
  (`kernelProduct_sub_negOnePowCast_smul_kernelProduct_coefficientComparison_mem_coboundaries`);
* the unit laws, from gluing a PSS plane into either input
  (`TauCeti.Floer.kernelProduct_coordinates_symm_sub_mem_coboundaries_right` and
  `TauCeti.Floer.kernelProduct_coordinates_symm_sub_mem_coboundaries_left`).

Together with the index conditions of rigid moduli spaces
(`TauCeti.Floer.kernelProduct_coefficientComparison_mem_cochain_gradeBy`), the Leibniz identity
(`TauCeti.Floer.kernelMap_kernelProduct_coefficientComparison_self_eq_add`) and the closedness
of the fundamental cycle (`TauCeti.Floer.coordinates_symm_coefficientComparison_mem_cocycles_zero`),
these make the degree-wise cohomology of `d` a graded ring with unit the class of `e`
(`TauCeti.Floer.cohomologyGRingOfCounts`), through `LinearMap.cohomologyGRing`, and a graded
algebra over the ground ring (`TauCeti.Floer.cohomologyGAlgebraOfCounts`). So `⨁ k, H^k` is an
algebra in which `of i [a] * of j [b] = of (i + j) [a ⋆ b]`
(`TauCeti.Floer.cohomologyGRingOfCounts_of_mk_mul_of_mk`) and `1 = of 0 [e]`
(`TauCeti.Floer.cohomologyGRingOfCounts_one`), although the chain-level product need not be
associative or unital. It is graded commutative when the input-exchange family exists
(`TauCeti.Floer.cohomologyGRingOfCounts_of_mul_of_comm`).

The construction applies to any capped complex with class-indexed product counts, for instance to
capped Morse generators with the counts of the Morse quantum product. The energy, compactness,
index and boundary-count hypotheses are the ones the geometric moduli spaces are to supply; no
moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich, 1995, for the associativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1, on the pair-of-pants product.
-/

public section

noncomputable section

namespace TauCeti.Floer

open DirectSum NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section Ring

variable [CommRing R] {ι : Type*} [Fintype ι] {P : ι → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P i)] (r : ∀ i, P i) {F : (Σ i, P i) → ℝ}
  (hF : ∀ i γ (D : P i), F ⟨i, γ +ᵥ D⟩ = F ⟨i, D⟩ - (-area ω c) γ)
  {μ : (Σ i, P i) → ℤ} (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩)
  (n : ℤ) (D : ι → ι → NovikovSeries R G ωG) {C : ℝ}
  (hδ : ∀ p p', mapKernelOfMatrix r r (fun i k => coefficientComparison q hq (D i k)) p p' ≠ 0 →
    F p' ≤ F p + C)
  (Q : ι → ι → ι → NovikovSeries R G ωG) {CQ : ℝ}
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r r r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F p₀ ≤ F p₁ + F p₂ + CQ)

section Laws

include hμ

/-- **Associativity of class-indexed counts on a complex, on cocycles.** Let `⋆` be the
ground-ring bilinear map of the counts `Q` of rigid pairs of pants with all three ends in the same
complex. If some family `K` of counts of rigid members of the one-parameter family of
four-punctured spheres, which lowers the cochain degree by one, satisfies the associativity
identity of `TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add` with
`Q` for all four products, then `(a ⋆ b) ⋆ c - a ⋆ (b ⋆ c)` is a coboundary of the cylinder
differential for all cocycles `a`, `b`, `c`. -/
theorem kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries
    (hassoc : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
      (∀ i j k l, ∀ A ∈ (K i j k l).support,
        μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
      ∀ i j k l, ∑ t, Q i j t * Q t k l - ∑ u, Q j k u * Q i u l =
        ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
          negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
          negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)
    {i j k : ℤ} {a b c : NovikovModule R F}
    (ha : a ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) i)
    (hb : b ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) j)
    (hc : c ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) k) :
    kernelProduct hnQ (kernelOfMatrix_mem hF r r r _)
          (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b) c -
        kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a
          (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) b c) ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) (i + j + k) := by
  obtain ⟨K, hK, hA⟩ := hassoc
  simpa only [novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ] using
    novikovProductOfMatrix_coefficientComparison_assoc_sub_mem_coboundaries r r r q hq r r r hF hF
      hF hF hμ hμ hF hF hμ hμ Q Q Q Q K D D D D n hδ hδ hδ hδ hK hA ha hb hc

/-- **Graded commutativity of class-indexed counts on a complex, on cocycles.** Let `⋆` be the
ground-ring bilinear map of the counts `Q` of rigid pairs of pants with all three ends in the same
complex. If some family `K` of counts of rigid members of the input-exchange family, which lowers
the cochain degree by one, satisfies the identity of
`novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_coefficientComparison`
between `Q` and `Q` with its two inputs exchanged, then `a ⋆ b - (-1)^(e f) b ⋆ a` is a coboundary
of the cylinder differential for all cocycles `a` and `b` of cochain degrees `e` and `f`. -/
theorem kernelProduct_sub_negOnePowCast_smul_kernelProduct_coefficientComparison_mem_coboundaries
    (hcomm : ∃ K : ι → ι → ι → NovikovSeries R G ωG,
      (∀ i j k, ∀ A ∈ (K i j k).support,
        μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n + 1) ∧
      ∀ i j l, Q i j l - negOnePowCast R ((n - μ ⟨i, r i⟩) * (n - μ ⟨j, r j⟩)) • Q j i l =
        ∑ k, K i j k * D k l + ∑ k, D i k * K k j l +
          negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * K i k l)
    {e f : ℤ} {a b : NovikovModule R F}
    (ha : a ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) e)
    (hb : b ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) f) :
    kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b -
        negOnePowCast R (e * f) • kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) b a ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).coboundaries
        (gradeBy R F fun p => n - μ p) (e + f) := by
  obtain ⟨K, hK, hC⟩ := hcomm
  simpa only [novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ] using
    novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_mem_coboundaries r r r q
      hq hF hF hF hμ hμ Q Q K D D D n hμ hK hC hδ hδ hδ ha hb

end Laws

section CohomologyRing

variable
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n)
  (hL : ∀ i j l, ∑ k, Q i j k * D k l =
    ∑ k, D i k * Q k j l + negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * Q i k l)
  (E : ι → NovikovSeries R G ωG)
  (hE : ∀ i, ∀ A ∈ (E i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n)
  (hED : ∀ l, ∑ i, E i * D i l = 0)

omit [Fintype ι] in
include hμ hQ in
/-- **The degree of the product of class-indexed counts on a complex.** If the counts `Q` of rigid
pairs of pants with all three ends in the same complex satisfy the index condition `hQ`, then their
ground-ring bilinear map adds cochain degrees `n - μ`. -/
theorem kernelProduct_coefficientComparison_mem_cochain_gradeBy [Finite ι] {i j : ℤ}
    {a b : NovikovModule R F} (ha : a ∈ gradeBy R F (fun p => n - μ p) i)
    (hb : b ∈ gradeBy R F (fun p => n - μ p) j) :
    kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b ∈
      gradeBy R F (fun p => n - μ p) (i + j) :=
  kernelProduct_mem_cochain_gradeBy hnQ _
    (grading_eq_of_kernelOfMatrix_coefficientComparison_ne_zero r r r q hq hμ hμ hμ hQ) ha hb

include hμ hL in
/-- **The Leibniz rule for class-indexed counts on a complex.** This is
`TauCeti.Floer.kernelMap_kernelProduct_coefficientComparison_eq_add` when all three ends of the
pairs of pants lie in the same complex: if the counts satisfy the Leibniz identity `hL`, then
`d (a ⋆ b) = d a ⋆ b + (-1)^e a ⋆ d b` for `a` of cochain degree `e`. -/
theorem kernelMap_kernelProduct_coefficientComparison_self_eq_add {e : ℤ}
    {a : NovikovModule R F} (ha : a ∈ gradeBy R F (fun p => n - μ p) e) (b : NovikovModule R F) :
    kernelMap hδ (mapKernelOfMatrix_mem hF r r _)
        (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b) =
      kernelProduct hnQ (kernelOfMatrix_mem hF r r r _)
          (kernelMap hδ (mapKernelOfMatrix_mem hF r r _) a) b +
        negOnePowCast R e • kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a
          (kernelMap hδ (mapKernelOfMatrix_mem hF r r _) b) :=
  kernelMap_kernelProduct_coefficientComparison_eq_add r r r q hq hF hF hF hμ Q D D D n hL hδ hδ hδ
    hnQ ha b

include hμ hE hED in
/-- **The unit cocycle of class-indexed counts.** If the counts `E` of rigid PSS planes
constrained by the fundamental cycle satisfy the index condition `hE` and the closedness
`∑ᵢ Eᵢ Dᵢₗ = 0`, then their combination is a cocycle of cochain degree zero. -/
theorem coordinates_symm_coefficientComparison_mem_cocycles_zero :
    ((coordinates hF r).symm fun i => coefficientComparison q hq (E i)) ∈
      (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
        (gradeBy R F fun p => n - μ p) 0 :=
  coordinates_symm_coefficientComparison_mem_cocycles r q hq hF hμ
    (fun i A hA => (hE i A hA).trans (sub_zero n).symm) hED hδ

variable [DecidableEq ι]
  (hone_mul : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1) ∧
    ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
  (hmul_one : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)
  (hassoc : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q i j t * Q t k l - ∑ u, Q j k u * Q i u l =
      ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
        negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)

/-- **The cohomology ring of class-indexed counts.** Let `d` be the ground-ring linear map of the
counts `D` of rigid Floer cylinders, `⋆` the ground-ring bilinear map of the counts `Q` of rigid
pairs of pants with all three ends in the same complex, and `e` the combination of the counts `E`
of rigid PSS planes, on the completed capped module graded by the cochain degree `n - μ`. Suppose
that the counts satisfy the index conditions of rigid moduli spaces, the Leibniz identity `hL` and
the closedness `∑ᵢ Eᵢ Dᵢₗ = 0` of the fundamental cycle, and that families of counts lowering the
cochain degree by one give the unit homotopies `hone_mul` (a plane glued into the first input) and
`hmul_one` (into the second) and the associativity homotopy `hassoc` of the four-punctured sphere.
Then the degree-wise cohomology of `d` is a graded ring, with product induced by `⋆` and unit the
class of `e`. -/
abbrev cohomologyGRingOfCounts :
    DirectSum.GRing fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) k :=
  LinearMap.cohomologyGRing (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc)

/-- In the cohomology ring of class-indexed counts, the product of the classes of two cocycles
`a` and `b` is the class of `a ⋆ b`. -/
theorem cohomologyGRingOfCounts_of_mk_mul_of_mk {i j : ℤ}
    (a : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) i)
    (b : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) j) :
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    of _ i (Submodule.Quotient.mk a) * of _ j (Submodule.Quotient.mk b) =
      of (fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
          (gradeBy R F fun p => n - μ p) k) (i + j)
        (Submodule.Quotient.mk ⟨kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b,
          LinearMap.apply_mem_cocycles_add _
            (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
            (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ
              hL) a.property b.property⟩) :=
  LinearMap.cohomologyGRing_of_mk_mul_of_mk (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc) a b

/-- The unit of the cohomology ring of class-indexed counts is the class of the combination of
the counts of PSS planes, in degree zero. -/
theorem cohomologyGRingOfCounts_one :
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    (1 : ⨁ k, (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
        (gradeBy R F fun p => n - μ p) k) =
      of (fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
          (gradeBy R F fun p => n - μ p) k) 0
        (Submodule.Quotient.mk
          ⟨(coordinates hF r).symm fun i => coefficientComparison q hq (E i),
            coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE
              hED⟩) :=
  LinearMap.cohomologyGRing_one (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc)

/-- **The cohomology algebra of class-indexed counts.** The graded ring
`TauCeti.Floer.cohomologyGRingOfCounts` is a graded algebra over the ground ring, with structure
map `x ↦ x • [e]` into degree zero, so that `⨁ k, H^k` is an algebra over the ground ring. -/
abbrev cohomologyGAlgebraOfCounts :
    @DirectSum.GAlgebra ℤ R (fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) k) _ _ _ _
      (cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
        hassoc).toGSemiring :=
  LinearMap.cohomologyGAlgebra (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc)

/-- **Graded commutativity of the cohomology ring of class-indexed counts.** If, in addition to
the hypotheses of `TauCeti.Floer.cohomologyGRingOfCounts`, some family `K` of counts of rigid
members of the input-exchange family, which lowers the cochain degree by one, gives a homotopy
between `Q` and `Q` with its inputs exchanged, then `x y = (-1)^(i j) y x` in the cohomology ring
for classes `x` and `y` of cochain degrees `i` and `j`. -/
theorem cohomologyGRingOfCounts_of_mul_of_comm
    (hcomm : ∃ K : ι → ι → ι → NovikovSeries R G ωG,
      (∀ i j k, ∀ A ∈ (K i j k).support,
        μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n + 1) ∧
      ∀ i j l, Q i j l - negOnePowCast R ((n - μ ⟨i, r i⟩) * (n - μ ⟨j, r j⟩)) • Q j i l =
        ∑ k, K i j k * D k l + ∑ k, D i k * K k j l +
          negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * K i k l)
    {i j : ℤ}
    (x : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) i)
    (y : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) j) :
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    of _ i x * of _ j y = negOnePowCast R (i * j) • (of _ j y * of _ i x) :=
  LinearMap.cohomologyGRing_of_mul_of_comm (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _))
    (kernelProduct_coefficientComparison_mem_cochain_gradeBy q hq r hF hμ n Q hnQ hQ)
    (kernelMap_kernelProduct_coefficientComparison_self_eq_add q hq r hF hμ n D hδ Q hnQ hL)
    _ (coordinates_symm_coefficientComparison_mem_cocycles_zero q hq r hF hμ n D hδ E hE hED)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_right r q hq hF r hF hμ D hδ Q hnQ E
      hone_mul)
    (kernelProduct_coordinates_symm_sub_mem_coboundaries_left r q hq hF r hF hμ D hδ Q hnQ E
      hmul_one)
    (kernelProduct_kernelProduct_coefficientComparison_sub_mem_coboundaries q hq r hF hμ n D hδ Q
      hnQ hassoc)
    (kernelProduct_sub_negOnePowCast_smul_kernelProduct_coefficientComparison_mem_coboundaries q hq
      r hF hμ n D hδ Q hnQ hcomm) x y

end CohomologyRing

end Ring

end TauCeti.Floer

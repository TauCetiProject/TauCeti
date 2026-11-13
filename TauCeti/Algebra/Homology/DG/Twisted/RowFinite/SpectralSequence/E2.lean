/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.SpectralSequence.FirstDifferential

/-!
# The second page of a row-finite index spectral sequence

Let `m` be a one-sided row-finite twisting cocycle on an arbitrary graded set of generators `P`,
with values in a DG algebra `A`, and let `ℳ` be a DG right `A`-module. The entries `m x y`
between generators whose indices differ by one are cycles of degree zero
(`TauCeti.RowFiniteTwistingCocycle.m_mem_zero_of_eq_add_one`,
`TauCeti.RowFiniteTwistingCocycle.d_m_eq_zero_of_eq_add_one`), so they act on the cohomology of
`ℳ`. The **classical complex** in coefficient degree `k` has in degree `q` the direct sum over the
generators of index `q` of the cohomology `H^k(ℳ)`, and as differential the matrix of these
actions, twisted by the Koszul sign. Each row of the cocycle is finite, so the matrix sends each
summand into finitely many summands. It squares to zero by the twisting equation at index
difference two (`TauCeti.RowFiniteTwistingCocycle.sum_subtype_m_mul_m_of_eq_add_two`) and the
Leibniz rule.

Under the splitting of the first page of the row-finite index spectral sequence into a direct sum
of copies of the cohomology of `ℳ` (`TauCeti.rowFiniteIndexGradedPieceHomologyIso`), the first
differential is the classical differential
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD`),
so the second page is the cohomology of the classical complex: the `E²` term of BDHO (Ch. 3,
§4.2), here for an arbitrary set of generators.

This extends `TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIso` from finitely many
generators, where the classical complex is a product, to row-finite cocycles, where it is a direct
sum.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.indexClassicalEntry`: the action of `m x y` on cohomology.
* `TauCeti.RowFiniteTwistingCocycle.indexClassicalD`: the matrix of the entries.
* `TauCeti.RowFiniteTwistingCocycle.indexClassicalComplex`: the classical complex in coefficient
  degree `k`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.indexClassicalD_comp`: the classical differential squares to
  zero.
* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD`:
  the first differential of the index spectral sequence is the classical differential.
* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceSecondPageXIso`: the second page of the
  row-finite index spectral sequence at `(a, b)` is the homology in degree `b + 1` of the
  classical complex in coefficient degree `a + 2 * b + 1`.

## Implementation notes

The pages are numbered as in Mathlib's `CochainComplex.spectralSequence`: the first page `E₁` is
`page 2` and the second page `E₂` is `page 3`. The object at `(a, b)` of `page 2` is the
cohomology in total degree `a + b` of the graded piece of index `b + 1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ} {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}

namespace RowFiniteTwistingCocycle

variable {m : RowFiniteTwistingCocycle 𝒜 dA P ind} (hM : IsDGRightModule hA ℳ dM)
  (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) (k : ℤ)

/-! ### The classical complex -/

/-- The entry of the classical complex in coefficient degree `k` between a generator `x` of index
`q + 1` and a generator `y` of index `q`: the action of the cycle `m x y` of degree zero on the
cohomology of `ℳ` in degree `k`, twisted by the Koszul sign. -/
noncomputable def indexClassicalEntry (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q}) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1)) ⟶
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  shiftedModuleComplexActHomology hM (m.m_mem_zero_of_subtype x y)
    (m.d_m_eq_zero_of_subtype hm x y) q (k - (q + 1)) (k - q) (by ring)

/-- **The entries of the classical differential, on classes**: the entry between generators `x` of
index `q + 1` and `y` of index `q` sends the class of a cycle `α` of `ℳ` to the class of
`op (m x y) • ε α`, with `ε` the Koszul sign. -/
theorem indexClassicalEntry_homologyπ (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q})
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X (k - (q + 1)))
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d _ (k - (q + 1) + 1)).hom α = 0)
    (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X (k - q))
    (hβ : (shiftedModuleComplexXEquiv hM q (k - q) β : M) =
      op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (q + 1) _ α : M))
    (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d (k - q) (k - q + 1)).hom β = 0) :
    (indexClassicalEntry hM hm k q x y).hom
        (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ _).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α _
            (by simp) hα)) =
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ _).hom
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β _ (by simp) hβ') :=
  shiftedModuleComplexActHomology_homologyπ hM _ _ q _ _ _ α hα β hβ hβ'

/-- **Representatives for the entries of the classical differential**: the image of the class of a
cycle `α` of `ℳ` under the entry between generators `x` of index `q + 1` and `y` of index `q` is
the class of a cycle `β` given by `op (m x y) • ε α`, with `ε` the Koszul sign. -/
theorem exists_indexClassicalEntry_homologyπ (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q})
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).X (k - (q + 1)))
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).d _ (k - (q + 1) + 1)).hom α = 0) :
    ∃ (β : (shiftedModuleComplex.{uR, uA, uM, uP} hM q).X (k - q))
      (hβ' : ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).d (k - q) (k - q + 1)).hom β = 0),
      (shiftedModuleComplexXEquiv hM q (k - q) β : M) =
        op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
          (shiftedModuleComplexXEquiv hM (q + 1) _ α : M) ∧
      (indexClassicalEntry hM hm k q x y).hom
          (((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homologyπ _).hom
            ((shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).moduleCatCyclesMk α _
              (by simp) hα)) =
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).homologyπ _).hom
          ((shiftedModuleComplex.{uR, uA, uM, uP} hM q).moduleCatCyclesMk β _ (by simp) hβ') :=
  exists_shiftedModuleComplexActHomology_homologyπ hM _ _ q _ _ _ α hα

/-- An entry of the classical complex vanishes when the corresponding entry of the cocycle
does. -/
theorem indexClassicalEntry_eq_zero (q : ℤ) (x : {x : P // ind x = q + 1})
    (y : {y : P // ind y = q}) (hxy : m.m x y = 0) : indexClassicalEntry hM hm k q x y = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1)).exists_homologyπ_moduleCatCyclesMk_eq (k - (q + 1) + 1) (by simp) c
  obtain ⟨β, hβ', hβ, hβπ⟩ := exists_indexClassicalEntry_homologyπ hM hm k q x y α hα
  rw [hβπ, ModuleCat.hom_zero, LinearMap.zero_apply]
  refine shiftedModuleComplex_homologyπ_eq_zero hM q (k - q) β hβ' 0 ?_
  simp [hβ, hxy]

/-- The differential of the classical complex in coefficient degree `k`, from the generators of
index `q + 1` to those of index `q`: on the summand of a generator `x`, the sum of the entries
`indexClassicalEntry` over the finitely many generators in the row of `x`. -/
noncomputable def indexClassicalD (q : ℤ) :
    (∐ fun _ : {x : P // ind x = q + 1} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM (q + 1)).homology (k - (q + 1))) ⟶
      ∐ fun _ : {y : P // ind y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  Sigma.desc fun x ↦ ∑ y ∈ m.indexRowSupport q x,
    indexClassicalEntry hM hm k q x y ≫
      Sigma.ι (fun _ : {y : P // ind y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) y

/-- The components of the classical differential are the entries `indexClassicalEntry`. -/
@[reassoc (attr := simp)]
theorem ι_indexClassicalD (q : ℤ) (x : {x : P // ind x = q + 1}) :
    Sigma.ι _ x ≫ indexClassicalD hM hm k q =
      ∑ y ∈ m.indexRowSupport q x, indexClassicalEntry hM hm k q x y ≫
        Sigma.ι (fun _ : {y : P // ind y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) y :=
  Sigma.ι_comp_desc _ _

/-- The components of the classical differential, as a sum over any finite set of generators
containing those in the row of `x`. -/
theorem ι_indexClassicalD_eq_sum (q : ℤ) (x : {x : P // ind x = q + 1})
    (T : Finset {y : P // ind y = q}) (hT : ∀ y ∉ T, m.m x y = 0) :
    Sigma.ι _ x ≫ indexClassicalD hM hm k q =
      ∑ y ∈ T, indexClassicalEntry hM hm k q x y ≫
        Sigma.ι (fun _ : {y : P // ind y = q} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) y := by
  rw [ι_indexClassicalD]
  refine Finset.sum_subset (fun y hy ↦ ?_) fun y _ hy ↦ ?_
  · by_contra hyT
    exact m.mem_indexRowSupport_iff.1 hy (hT y hyT)
  · rw [indexClassicalEntry_eq_zero hM hm k q x y (not_not.1 (m.mem_indexRowSupport_iff.not.1 hy)),
      zero_comp]

/-- **The classical differential squares to zero, entrywise**: for generators `x` of index
`q + 2` and `z` of index `q`, the sum, over a finite set of generators `y` of index `q + 1`
containing those in the row of `x`, of the composites of the entries vanishes. On a class `[α]`,
the sum is the class of `op (∑ y, m x y * m y z) • α`, which is `-op (d (m x z)) • α` by the
twisting equation, a coboundary by the Leibniz rule. -/
theorem sum_indexClassicalEntry_comp (q : ℤ) (x : {x : P // ind x = q + 1 + 1})
    (z : {z : P // ind z = q}) (T : Finset {y : P // ind y = q + 1})
    (hT : ∀ y ∉ T, m.m x y = 0) :
    ∑ y ∈ T, indexClassicalEntry hM hm k (q + 1) x y ≫ indexClassicalEntry hM hm k q y z = 0 := by
  have hx := x.2
  have hz := z.2
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1 + 1)).exists_homologyπ_moduleCatCyclesMk_eq (k - (q + 1 + 1) + 1) (by simp) c
  choose β hβ' hβ hβπ using fun y ↦ exists_indexClassicalEntry_homologyπ hM hm k (q + 1) x y α hα
  choose γ hγ' hγ hγπ using fun y ↦
    exists_indexClassicalEntry_homologyπ hM hm k q y z (β y) (hβ' y)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, hβπ, hγπ]
  rw [← map_sum, HomologicalComplex.sum_moduleCatCyclesMk]
  -- Reduction to representatives is done; `α₀` is the underlying cycle of `ℳ` of degree `k`.
  set α₀ := (shiftedModuleComplexXEquiv hM (q + 1 + 1) _ α : M)
  have hα₀ : α₀ ∈ ℳ k := shiftedModuleComplexXEquiv_mem hM (by ring) α
  have hdα₀ : dM α₀ = 0 := (shiftedModuleComplexXEquiv_d_eq_zero_iff hM _ _ α).1 hα
  have hb : -((k.negOnePow : ℤ) • (op (m.m x z) • α₀)) ∈ ℳ (k - q - 1 + q) := by
    have hdeg : k - q - 1 + q = k + -1 := by ring
    rw [hdeg]
    exact neg_mem (zsmul_mem (op_smul_mem_of_mem_graded (m.m_mem_neg_one_of_eq_add_two
      (by rw [hx, hz]; ring)) hα₀) _)
  -- The sum of the composites is a boundary: it is `dM` of the element `hb`-membership provides.
  refine shiftedModuleComplex_homologyπ_eq_zero hM q (k - q) _ _
    ((shiftedModuleComplexXEquiv hM q _).symm ⟨_, hb⟩) ?_
  rw [LinearEquiv.apply_symm_apply, map_sum, Submodule.coe_sum]
  simp only [hγ, hβ]
  -- The twisting equation at index difference two: the double action is by `∑ y, m x y * m y z`.
  rw [Finset.sum_congr rfl fun y _ ↦ op_smul_koszulTwist_op_smul_koszulTwist
      (m.m_mem_zero_of_subtype x y) hα₀ 1,
    ← Finset.sum_smul, ← Finset.op_sum, m.sum_subtype_m_mul_m_of_eq_add_two hm q x.2 z.2 T hT]
  -- The Leibniz rule for the cycle `α₀` and the entry `m x z` of degree `-1`.
  have hl := hM.leibniz hα₀ (m.m x z)
  rw [hdα₀, smul_zero, zero_add] at hl
  simp [hl, ← Units.smul_def, smul_smul]

/-- **The classical differential squares to zero**, by `sum_indexClassicalEntry_comp`. -/
theorem indexClassicalD_comp (q : ℤ) :
    indexClassicalD hM hm k (q + 1) ≫ indexClassicalD hM hm k q = 0 := by
  classical
  refine Sigma.hom_ext _ _ fun x ↦ ?_
  -- The generators `z` of index `q` occurring in the row of some `y` in the row of `x`.
  set U := (m.indexRowSupport (q + 1) x).biUnion fun y ↦ m.indexRowSupport q y
  rw [ι_indexClassicalD_assoc, comp_zero, Preadditive.sum_comp]
  have hU : ∀ y ∈ m.indexRowSupport (q + 1) x,
      Sigma.ι _ y ≫ indexClassicalD hM hm k q =
        ∑ z ∈ U, indexClassicalEntry hM hm k q y z ≫
          Sigma.ι (fun _ : {z : P // ind z = q} ↦
            (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) z := fun y hy ↦
    ι_indexClassicalD_eq_sum hM hm k q y U fun z hz ↦ by
      by_contra hyz
      exact hz (Finset.mem_biUnion.2 ⟨y, hy, m.mem_indexRowSupport_iff.2 hyz⟩)
  rw [Finset.sum_congr rfl fun y hy ↦ by rw [Category.assoc, hU y hy]]
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  rw [sum_indexClassicalEntry_comp hM hm k q x z _ fun y hy ↦ by
      simpa using m.mem_indexRowSupport_iff.not.1 hy, zero_comp]

/-- **The classical complex** in coefficient degree `k`: in degree `q`, the direct sum over the
generators of index `q` of the cohomology of `ℳ` in degree `k` (as the cohomology of
`shiftedModuleComplex hM q` in degree `k - q`), with the differential `indexClassicalD`, the matrix
of the actions of the entries `m x y` between generators whose indices differ by one. -/
noncomputable def indexClassicalComplex : ChainComplex (ModuleCat.{max uM uP} R) ℤ :=
  ChainComplex.of
    (fun q ↦ ∐ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q))
    (indexClassicalD hM hm k) (indexClassicalD_comp hM hm k)

/-- The degree-`q` term of the classical complex is the direct sum over the generators of index
`q` of the cohomology of `ℳ` in degree `k`. -/
noncomputable def indexClassicalComplexXIso (q : ℤ) :
    (indexClassicalComplex hM hm k).X q ≅ ∐ fun _ : {x : P // ind x = q} ↦
      (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q) :=
  -- The terms of `ChainComplex.of` are the given family of objects.
  Iso.refl _

private theorem indexClassicalComplex_d_eq (q : ℤ) :
    (indexClassicalComplex hM hm k).d (q + 1) q = indexClassicalD hM hm k q := by
  unfold indexClassicalComplex
  exact ChainComplex.of_d (fun q ↦ ∐ fun _ : {x : P // ind x = q} ↦
    (shiftedModuleComplex.{uR, uA, uM, uP} hM q).homology (k - q)) (indexClassicalD hM hm k) q

/-- **The differential of the classical complex is `indexClassicalD`**, under the identification
`indexClassicalComplexXIso` of its terms with direct sums of cohomology. (The plain equation
`d (q + 1) q = indexClassicalD` typechecks only by unfolding the terms of `ChainComplex.of`, so
the statement is phrased through `indexClassicalComplexXIso`.) -/
theorem indexClassicalComplexXIso_inv_comp_d_comp_hom (q : ℤ) :
    (indexClassicalComplexXIso hM hm k (q + 1)).inv ≫ (indexClassicalComplex hM hm k).d (q + 1) q ≫
      (indexClassicalComplexXIso hM hm k q).hom = indexClassicalD hM hm k q := by
  rw [indexClassicalComplex_d_eq]
  -- Both identifications are the identity, by definition of `indexClassicalComplexXIso`.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-! ### The first differential is the classical differential -/

/-- **The first differential of the row-finite index spectral sequence on one generator.** Under
the identification of the first page with the cohomology of the graded pieces, the differential
from `pq` to `pq'`, restricted to the summand of a generator `x` of index `q + 1`, is the sum over
the generators `y` of index `q` in the row of `x` of the action of `m x y` on the cohomology of
`ℳ`, followed by the insertion at `y`. The indices are given with equations, as in
`indexSpectralSequenceFirstPageXIsoOfEq`. -/
@[reassoc]
theorem homologyMap_single_comp_page_two_d (pq pq' : ℤ × ℤ) (hpq' : pq' = (pq.1 + 2, pq.2 - 1))
    (q i₁ n n' : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2) (hq' : q = pq'.2 + 1)
    (hn : n = pq.1 + pq.2) (hn' : n' = pq'.1 + pq'.2) (x : {x : P // ind x = q + 1}) :
    HomologicalComplex.homologyMap (rowFiniteIndexGradedPieceSingle hM ind x) n ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq q (q + 1) hq (by rw [hq]) n hn).inv ≫
        ((m.indexSpectralSequence hM hm).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq' i₁ q hi₁ hq' n' hn').hom =
      ∑ y ∈ m.indexRowSupport q x,
        shiftedModuleComplexActHomology hM (m.m_mem_zero_of_subtype x y)
          (m.d_m_eq_zero_of_subtype hm x y) q n n'
          (by rw [hn, hn', hpq']; dsimp only; ring) ≫
        HomologicalComplex.homologyMap (rowFiniteIndexGradedPieceSingle hM ind y) n' := by
  obtain ⟨a, b⟩ := pq
  subst hpq'
  dsimp only at hq hi₁ hq' hn hn'
  subst hq hi₁ hn
  obtain rfl : n' = a + q + 1 := by rw [hn']; ring
  ext c : 2
  obtain ⟨α, hα, rfl⟩ := (shiftedModuleComplex.{uR, uA, uM, uP} hM
    (q + 1)).exists_homologyπ_moduleCatCyclesMk_eq (a + q + 1) (by simp) c
  have h1 := fun y : {y : P // ind y = q} ↦ exists_shiftedModuleComplexActHomology_homologyπ hM
    (m.m_mem_zero_of_subtype x y) (m.d_m_eq_zero_of_subtype hm x y) q (a + q) (a + q + 1)
    (by ring) α hα
  choose β hβ' hβ hβπ using h1
  -- Each representative `β y` is the action of `m x y` on `α`.
  have hβeq : ∀ y, β y = shiftedModuleComplexActX hM (m.m_mem_zero_of_subtype x y) q (a + q) α :=
    fun y ↦ (shiftedModuleComplexXEquiv hM q _).injective (Subtype.ext (by
      rw [hβ y, shiftedModuleComplexXEquiv_shiftedModuleComplexActX]))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply]
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk,
    m.indexSpectralSequence_page_two_d_apply hM hm a q _
      (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero _ _ _ _ hα)]
  simp only [hβπ, HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  rw [← map_sum, HomologicalComplex.sum_moduleCatCyclesMk]
  congr 1
  refine (rowFiniteIndexGradedPieceComplex ind hM q).moduleCat_iCycles_injective _ ?_
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk,
    m.indexGradedPieceD1X_single]
  simp only [hβeq]

/-- **The first differential of the row-finite index spectral sequence is the classical
differential**: under the identifications of the first page with the direct sums of the
cohomology of `ℳ` (`indexSpectralSequenceFirstPageXIsoOfEq` followed by
`rowFiniteIndexGradedPieceHomologyIso`), the differential from `pq` to `pq'` is
`indexClassicalD`. -/
theorem indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD (pq pq' : ℤ × ℤ)
    (hpq' : pq' = (pq.1 + 2, pq.2 - 1)) (q i₁ : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2)
    (hq' : q = pq'.2 + 1) (hn : k - (q + 1) = pq.1 + pq.2) (hn' : k - q = pq'.1 + pq'.2) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq q (q + 1) hq (by rw [hq]) _ hn).hom ≫
        (rowFiniteIndexGradedPieceHomologyIso hM ind _).hom ≫ indexClassicalD hM hm k q =
      ((m.indexSpectralSequence hM hm).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq' i₁ q hi₁ hq' _ hn').hom ≫
        (rowFiniteIndexGradedPieceHomologyIso hM ind _).hom := by
  refine (cancel_epi ((rowFiniteIndexGradedPieceHomologyIso hM ind _).inv ≫
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq q (q + 1) hq (by rw [hq]) _ hn).inv)).1 ?_
  refine Sigma.hom_ext _ _ fun x ↦ ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ι_rowFiniteIndexGradedPieceHomologyIso_inv_assoc,
    ι_indexClassicalD]
  rw [homologyMap_single_comp_page_two_d_assoc hM hm pq pq' hpq' q i₁ _ _ hq hi₁ hq' hn hn' x]
  simp only [Preadditive.sum_comp, Category.assoc,
    homologyMap_rowFiniteIndexGradedPieceSingle_comp_rowFiniteIndexGradedPieceHomologyIso_hom]
  simp only [indexClassicalEntry]

/-! ### The second page -/

/-- The first-page differential is the differential of the classical complex, under the
identifications of the first page with the terms of the classical complex. -/
private theorem secondPage_square (pq pq' : ℤ × ℤ) (hpq' : pq' = (pq.1 + 2, pq.2 - 1))
    (q i₁ : ℤ) (hq : q = pq.2) (hi₁ : i₁ = pq'.2) (hq' : q = pq'.2 + 1)
    (hn : k - (q + 1) = pq.1 + pq.2) (hn' : k - q = pq'.1 + pq'.2) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq q (q + 1) hq (by rw [hq]) _ hn ≪≫
        rowFiniteIndexGradedPieceHomologyIso hM ind _).hom ≫
        (indexClassicalComplex hM hm k).d (q + 1) q =
      ((m.indexSpectralSequence hM hm).page 2).d pq pq' ≫
        (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm pq' i₁ q hi₁ hq' _ hn' ≪≫
          rowFiniteIndexGradedPieceHomologyIso hM ind _).hom := by
  rw [indexClassicalComplex_d_eq]
  exact (Category.assoc _ _ _).trans
    (indexSpectralSequenceFirstPageXIsoOfEq_comp_indexClassicalD hM hm k pq pq' hpq' q i₁ hq hi₁
      hq' hn hn')

/-- The short complex of the first page around `(a, b)` is isomorphic to the short complex of the
classical complex around degree `b + 1`: the isomorphism is the identification of each first-page
term with a direct sum of cohomology groups, which intertwines the differentials
(`secondPage_square`). -/
noncomputable def indexSecondPageShortComplexIso (a b : ℤ) :
    ((m.indexSpectralSequence hM hm).page 2).sc' (a - 2, b + 1) (a, b) (a + 2, b - 1) ≅
      (indexClassicalComplex hM hm (a + 2 * b + 1)).sc' (b + 1 + 1) (b + 1) b :=
  ShortComplex.isoMk
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a - 2, b + 1) (b + 1) (b + 1 + 1) rfl rfl
      (a + 2 * b + 1 - (b + 1 + 1)) (by dsimp only; ring) ≪≫
        rowFiniteIndexGradedPieceHomologyIso hM ind _)
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a, b) b (b + 1) rfl rfl
      (a + 2 * b + 1 - (b + 1)) (by dsimp only; ring) ≪≫
        rowFiniteIndexGradedPieceHomologyIso hM ind _)
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a + 2, b - 1) (b - 1) b rfl
      (by dsimp only; ring) (a + 2 * b + 1 - b) (by dsimp only; ring) ≪≫
        rowFiniteIndexGradedPieceHomologyIso hM ind _)
    (secondPage_square hM hm _ (a - 2, b + 1) (a, b)
      (Prod.ext (by dsimp only; ring) (by dsimp only; ring)) (b + 1) b rfl rfl
      (by dsimp only) (by dsimp only; ring) (by dsimp only; ring))
    (secondPage_square hM hm _ (a, b) (a + 2, b - 1) rfl b (b - 1) rfl rfl
      (by dsimp only; ring) (by dsimp only; ring) (by dsimp only; ring))

/-- The first component of `indexSecondPageShortComplexIso`: the first-page term at
`(a - 2, b + 1)` is identified with the direct sum of cohomology groups of `ℳ` (the term of the
classical complex being identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₁ (a b : ℤ) :
    (indexSecondPageShortComplexIso hM hm a b).hom.τ₁ ≫
        (indexClassicalComplexXIso hM hm (a + 2 * b + 1) (b + 1 + 1)).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a - 2, b + 1) (b + 1) (b + 1 + 1) rfl rfl
        (a + 2 * b + 1 - (b + 1 + 1)) (by dsimp only; ring) ≪≫
          rowFiniteIndexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- The second component of `indexSecondPageShortComplexIso`: the first-page term at `(a, b)` is
identified with the direct sum of cohomology groups of `ℳ` (the term of the classical complex
being identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₂ (a b : ℤ) :
    (indexSecondPageShortComplexIso hM hm a b).hom.τ₂ ≫
        (indexClassicalComplexXIso hM hm (a + 2 * b + 1) (b + 1)).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a, b) b (b + 1) rfl rfl
        (a + 2 * b + 1 - (b + 1)) (by dsimp only; ring) ≪≫
          rowFiniteIndexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- The third component of `indexSecondPageShortComplexIso`: the first-page term at
`(a + 2, b - 1)` is identified with the direct sum of cohomology groups of `ℳ` (the term of the
classical complex being identified by `indexClassicalComplexXIso`). -/
@[reassoc]
theorem indexSecondPageShortComplexIso_hom_τ₃ (a b : ℤ) :
    (indexSecondPageShortComplexIso hM hm a b).hom.τ₃ ≫
        (indexClassicalComplexXIso hM hm (a + 2 * b + 1) b).hom =
      (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a + 2, b - 1) (b - 1) b rfl
        (by dsimp only; ring) (a + 2 * b + 1 - b) (by dsimp only; ring) ≪≫
          rowFiniteIndexGradedPieceHomologyIso hM ind _).hom := by
  -- `indexClassicalComplexXIso` is the identity, and the component of `isoMk` is the given one.
  exact Category.comp_id _

/-- **The second page of the row-finite index spectral sequence is the cohomology of the
classical complex** (BDHO, Definition 3.38 and Ch. 3 §4.2): the object at `(a, b)` of the page `3`
of the index spectral sequence (the classical `E₂` page, in Mathlib's numbering of pages) is the
homology in degree `b + 1` of the classical complex in coefficient degree `a + 2 * b + 1`. It is
the homology of the first page at `(a, b)`, identified with the homology of the classical complex
by `indexSecondPageShortComplexIso` (see `indexSpectralSequenceSecondPageXIso_eq`). -/
noncomputable def indexSpectralSequenceSecondPageXIso (a b : ℤ) :
    ((m.indexSpectralSequence hM hm).page 3).X (a, b) ≅
      (indexClassicalComplex hM hm (a + 2 * b + 1)).homology (b + 1) :=
  ((m.indexSpectralSequence hM hm).iso 2 3 (a, b)).symm ≪≫
    ((m.indexSpectralSequence hM hm).page 2).homologyIsoSc' (a - 2, b + 1) (a, b) (a + 2, b - 1)
      ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
      ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
    ShortComplex.homologyMapIso (indexSecondPageShortComplexIso hM hm a b) ≪≫
    ((indexClassicalComplex hM hm (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
      (by simp) (by simp)).symm

/-- The second-page isomorphism is the inverse of the identification of the second page with the
homology of the first page, followed by the homology isomorphism of
`indexSecondPageShortComplexIso`. -/
theorem indexSpectralSequenceSecondPageXIso_eq (a b : ℤ) :
    indexSpectralSequenceSecondPageXIso hM hm a b =
      ((m.indexSpectralSequence hM hm).iso 2 3 (a, b)).symm ≪≫
        ((m.indexSpectralSequence hM hm).page 2).homologyIsoSc' (a - 2, b + 1) (a, b)
          (a + 2, b - 1)
          ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
          ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
        ShortComplex.homologyMapIso (indexSecondPageShortComplexIso hM hm a b) ≪≫
        ((indexClassicalComplex hM hm (a + 2 * b + 1)).homologyIsoSc' (b + 1 + 1) (b + 1) b
          (by simp) (by simp)).symm :=
  (rfl)

end RowFiniteTwistingCocycle

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Semicontinuity
public import TauCeti.RingTheory.Spectrum.Prime.Grauert

import TauCeti.RingTheory.Flat.Extensions

/-!
# Grauert's theorem for a complex of modules

Let `R` be a reduced ring and `K` a complex of `R`-modules, and fix a degree `j` with previous
degree `i` and next degree `k`. Suppose that `K.X i` is finite, `K.X j` finitely presented and
`K.X k` finite projective, and that the dimension of the homology in degree `j` of the fibre
`κ(p) ⊗_R K` is a locally constant function of `p ∈ Spec R`. Then:

* the homology `H_j(K)` is a finite projective `R`-module
  (`HomologicalComplex.projective_homology_of_isLocallyConstant`,
  `HomologicalComplex.finite_homology_of_isLocallyConstant`), whose rank at `p` is the dimension
  of the fibre homology at `p` (`HomologicalComplex.rankAtStalk_homology_of_isLocallyConstant`);
* its formation commutes with every base change: for every `R`-algebra `S`,
  `S ⊗_R H_j(K) ≅ H_j(S ⊗_R K)` (`HomologicalComplex.nonempty_linearEquiv_tensor_homology`);
* so does the homology in the previous degree `i`, when `K.X j` is flat:
  `S ⊗_R H_i(K) ≅ H_i(S ⊗_R K)` (`HomologicalComplex.nonempty_linearEquiv_tensor_homology_prev`);
  if moreover `K.X i` is flat and the differential into degree `i` is zero, `H_i(K)` is flat
  (`HomologicalComplex.flat_homology_prev_of_isLocallyConstant`).

This is the form in which the algebraic Grauert theorem
`LinearMap.homologyBaseChange_bijective_of_isLocallyConstant_finrank_fiber_homology` applies to a
complex in `ModuleCat R`, whose base change is taken with `ModuleCat.extendScalars`, as for the
finite projective complex computing the cohomology of every base change of a flat family of
coherent sheaves (`TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback`).
The homology of `K` and of `S ⊗_R K` is identified with kernels modulo images by
`HomologicalComplex.nonempty_linearEquiv_homology` and
`HomologicalComplex.nonempty_linearEquiv_homology_extendScalars`.

## References

* D. Mumford, *Abelian Varieties*, §5, Corollary 2.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.12.9.
-/

public section

noncomputable section

open CategoryTheory Limits Module TensorProduct

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

/-- The homology in degree `j` of a complex `K` of `R`-modules is the image of the kernel of
`d : K.X j → K.X k` in the cokernel of `d : K.X i → K.X j`, where `i` and `k` are the degrees
before and after `j`. -/
theorem nonempty_linearEquiv_homology {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k) :
    Nonempty (K.homology j ≃ₗ[R]
      (LinearMap.ker (K.d j k).hom).map (LinearMap.range (K.d i j).hom).mkQ) :=
  ⟨((K.homologyIsoSc' i j k hi hk) ≪≫ (K.sc' i j k).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
    LinearMap.mapMkQKerEquiv _ _ _⟩

private lemma d_comp_d_hom (i j k : ι) : (K.d j k).hom ∘ₗ (K.d i j).hom = 0 := by
  rw [← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]

/-- The fibre homology dimension of `K` in degree `j` agrees with that of the kernel modulo
image form. -/
lemma finrank_homology_extendScalars_eq {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          c).obj K).homology j) =
      finrank p.asIdeal.ResidueField
        ((LinearMap.ker ((K.d j k).hom.baseChange p.asIdeal.ResidueField)).map
          (LinearMap.range ((K.d i j).hom.baseChange p.asIdeal.ResidueField)).mkQ) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology_extendScalars p.asIdeal.ResidueField hi hk
  exact e.finrank_eq

variable [IsReduced R] {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
  (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
    ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
      c).obj K).homology j))

include hi hk h

omit [IsReduced R] in
/-- The locally constant fibre homology dimension in the kernel modulo image form of the
algebraic Grauert theorem. -/
lemma isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant :
    IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((LinearMap.ker ((K.d j k).hom.baseChange p.asIdeal.ResidueField)).map
        (LinearMap.range ((K.d i j).hom.baseChange p.asIdeal.ResidueField)).mkQ) := by
  convert h using 2 with p
  exact (K.finrank_homology_extendScalars_eq hi hk p).symm

/-- **Grauert's theorem: homology is finite.** Over a reduced ring, if `K.X j` is finite and
`K.X k` finite projective and the homology of the fibres `κ(p) ⊗_R K` in degree `j` has locally
constant dimension, then the homology of `K` in degree `j` is a finite `R`-module. -/
theorem finite_homology_of_isLocallyConstant [Module.Finite R (K.X j)] [Module.Finite R (K.X k)]
    [Module.Projective R (K.X k)] : Module.Finite R (K.homology j) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi hk
  have := LinearMap.finite_homology_of_isLocallyConstant_finrank_fiber_homology
    (K.d_comp_d_hom i j k) (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h)
  exact Module.Finite.equiv e.symm

/-- **Grauert's theorem: homology is projective.** Over a reduced ring, if `K.X i` is finite,
`K.X j` finitely presented and `K.X k` finite projective, and the homology of the fibres
`κ(p) ⊗_R K` in degree `j` has locally constant dimension, then the homology of `K` in degree `j`
is a projective `R`-module. -/
theorem projective_homology_of_isLocallyConstant [Module.Finite R (K.X i)]
    [Module.FinitePresentation R (K.X j)] [Module.Finite R (K.X k)]
    [Module.Projective R (K.X k)] : Module.Projective R (K.homology j) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi hk
  have := LinearMap.projective_homology_of_isLocallyConstant_finrank_fiber_homology
    (K.d_comp_d_hom i j k) (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h)
  exact Module.Projective.of_equiv e.symm

/-- **Grauert's theorem: homology commutes with base change.** Over a reduced ring, if `K.X j` is
finite and `K.X k` finite projective, and the homology of the fibres `κ(p) ⊗_R K` in degree `j`
has locally constant dimension, then for every `R`-algebra `S` the homology of `S ⊗_R K` in
degree `j` is `S ⊗_R H_j(K)`. -/
theorem nonempty_linearEquiv_tensor_homology [Module.Finite R (K.X j)] [Module.Finite R (K.X k)]
    [Module.Projective R (K.X k)] (S : Type u) [CommRing S] [Algebra R S] :
    Nonempty (S ⊗[R] K.homology j ≃ₗ[S]
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).obj K).homology j) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi hk
  obtain ⟨e'⟩ := K.nonempty_linearEquiv_homology_extendScalars S hi hk
  exact ⟨LinearEquiv.baseChange R S _ _ e ≪≫ₗ LinearEquiv.ofBijective _
    (LinearMap.homologyBaseChange_bijective_of_isLocallyConstant_finrank_fiber_homology S
      (K.d_comp_d_hom i j k)
      (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h)) ≪≫ₗ e'.symm⟩

/-- **Grauert's theorem: the rank of homology.** Over a reduced ring, if `K.X j` is finite and
`K.X k` finite projective, and the homology of the fibres `κ(p) ⊗_R K` in degree `j` has locally
constant dimension, then the rank of `H_j(K)` at `p` is the dimension of the homology in degree
`j` of the fibre `κ(p) ⊗_R K`. -/
theorem rankAtStalk_homology_of_isLocallyConstant [Module.Finite R (K.X j)]
    [Module.Finite R (K.X k)] [Module.Projective R (K.X k)] (p : PrimeSpectrum R) :
    rankAtStalk (K.homology j) p = finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        c).obj K).homology j) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi hk
  rw [rankAtStalk_eq_of_equiv e, K.finrank_homology_extendScalars_eq hi hk p]
  exact LinearMap.rankAtStalk_homology_eq_finrank_fiber_homology (K.d_comp_d_hom i j k)
    (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h) p

/-- **Grauert's theorem: the previous homology commutes with base change.** Over a reduced ring,
if `K.X j` is finite and `K.X k` finite projective, and the homology of the fibres `κ(p) ⊗_R K` in
degree `j` has locally constant dimension and `K.X j` is flat, then for every `R`-algebra `S` the
homology of `S ⊗_R K` in the degree `i` before `j` is `S ⊗_R H_i(K)`. No finiteness is needed in
degree `i` or below. -/
theorem nonempty_linearEquiv_tensor_homology_prev {i' : ι} (hi' : c.prev i = i')
    (hij : c.next i = j) [Module.Finite R (K.X j)] [Module.Flat R (K.X j)]
    [Module.Finite R (K.X k)] [Module.Projective R (K.X k)]
    (S : Type u) [CommRing S] [Algebra R S] :
    Nonempty (S ⊗[R] K.homology i ≃ₗ[S]
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).obj K).homology i) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi' hij
  obtain ⟨e'⟩ := K.nonempty_linearEquiv_homology_extendScalars S hi' hij
  -- The cokernel of `K.X i → K.X j` is flat by the algebraic Grauert theorem, and `K.X j` is
  -- flat, so homology in degree `i` commutes with every base change.
  have := LinearMap.flat_quotient_range_of_isLocallyConstant_finrank_fiber_homology
    (K.d_comp_d_hom i j k) (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h)
  exact ⟨LinearEquiv.baseChange R S _ _ e ≪≫ₗ LinearEquiv.ofBijective _
    (LinearMap.homologyBaseChange_bijective S (K.d_comp_d_hom i' i j)) ≪≫ₗ e'.symm⟩

/-- **Grauert's theorem: the previous homology is flat when it is a kernel.** Over a reduced ring,
if `K.X j` is finite and `K.X k` finite projective, and the homology of the fibres `κ(p) ⊗_R K` in
degree `j` has locally constant dimension, and `K.X i`, `K.X j` are flat and the differential into
degree `i` is zero, then the homology of `K` in degree `i`, the kernel of `d : K.X i → K.X j`, is
flat. This applies to the lowest degree of a complex concentrated in nonnegative degrees. -/
theorem flat_homology_prev_of_isLocallyConstant {i' : ι} (hi' : c.prev i = i')
    (hij : c.next i = j) (hd : K.d i' i = 0) [Module.Flat R (K.X i)] [Module.Finite R (K.X j)]
    [Module.Flat R (K.X j)] [Module.Finite R (K.X k)] [Module.Projective R (K.X k)] :
    Module.Flat R (K.homology i) := by
  obtain ⟨e⟩ := K.nonempty_linearEquiv_homology hi' hij
  have := LinearMap.flat_quotient_range_of_isLocallyConstant_finrank_fiber_homology
    (K.d_comp_d_hom i j k) (K.isLocallyConstant_finrank_fiber_homology_of_isLocallyConstant hi hk h)
  -- The homology in degree `i` sits in `0 → H_i → K.X i → range d → 0`, where `range d` is flat as
  -- a submodule of the flat module `K.X j` with flat quotient.
  have := (LinearMap.range (K.d i j).hom).flat_of_flat_quotient
  have : Module.Flat R (K.X i ⧸ LinearMap.range (K.d i' i).hom) :=
    Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot _ (by simp [hd]))
  have := LinearMap.flat_homology (K.d_comp_d_hom i' i j)
  exact Module.Flat.of_linearEquiv e

end HomologicalComplex

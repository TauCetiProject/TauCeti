/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.SpectralSequence
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Splitting
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# The first page of a row-finite index spectral sequence

Let `m` be a one-sided row-finite twisting cocycle on an arbitrary graded set of generators `P`,
and let `ℳ` be a DG right module. The graded piece of index `p` of the index filtration of the
row-finite twisted complex is the complex `TauCeti.rowFiniteIndexGradedPieceComplex` of
finite-support families of coefficients on the generators of index `p`, with the coefficient
differential `dM` in each coordinate. This file splits its cohomology as a direct sum, over the
generators of index `p`, of copies of the cohomology of `ℳ` shifted by `p`
(`TauCeti.shiftedModuleComplex hM p`, whose degree-`n` term is `ℳ (n + p)`).

The finite construction (`TauCeti.indexGradedPieceHomologyIso`) splits the cohomology as a
product, through the evaluations at the generators. For infinitely many generators the
finite-support families form a direct sum, not a product, so the splitting goes through the
insertions at the generators (`TauCeti.rowFiniteIndexGradedPieceSingle`) instead. They exhibit
the graded piece as a coproduct of copies of the shifted module complex, degreewise
(`TauCeti.isColimitRowFiniteIndexGradedPieceCofanX`) and hence as complexes
(`TauCeti.isColimitRowFiniteIndexGradedPieceCofan`). Coproducts of modules are exact, so
cohomology commutes with them
(`TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`).

Combined with the identification of the first page of the index spectral sequence with the
cohomology of the graded pieces
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`), the object at `(p, q)`
of the first page is the direct sum, over the generators of index `q + 1`, of copies of the
cohomology of `ℳ` in degree `p + 2 q + 1`
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIsoSigma`).

## Main definitions

* `TauCeti.rowFiniteIndexGradedPieceSingle hM ind x`: the insertion at a generator `x` of index
  `p`, as a morphism of complexes from `shiftedModuleComplex hM p` to the graded piece.
* `TauCeti.rowFiniteIndexGradedPieceHomologyIso`: the cohomology of the graded piece of index `p`
  is the coproduct over the generators of index `p` of the cohomology of
  `shiftedModuleComplex hM p`.
* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIsoSigma`: the first page of
  the row-finite index spectral sequence as a direct sum of copies of the cohomology of `ℳ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (hM : IsDGRightModule hA ℳ dM) (ind : P → ℤ) {p : ℤ}

/-! ### Insertion at a generator -/

/-- The value at a generator of index `p` of a family of total degree `n` lies in `ℳ (n + p)`. -/
theorem rowFiniteIndexGradedPieceComplexXEquiv_apply_mem (n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n) (x : {x // ind x = p}) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n f : {x // ind x = p} →₀ M) x ∈ ℳ (n + p) := by
  have hf := (mem_rowFiniteTotalGrading_iff ℳ _).1
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n f).2 x
  rwa [x.2] at hf

/-- The insertion at a generator `x` of index `p`, from `ℳ (n + p)` to the degree-`n` term of the
graded piece of index `p`. -/
noncomputable def rowFiniteIndexGradedPieceSingleX (x : {x // ind x = p}) (n : ℤ) :
    (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n →ₗ[R]
      (rowFiniteIndexGradedPieceComplex ind hM p).X n :=
  (rowFiniteIndexGradedPieceComplexXEquiv hM p n).symm.toLinearMap ∘ₗ
    ((Finsupp.lsingle x ∘ₗ (ℳ (n + p)).subtype).codRestrict _ fun α ↦
      (mem_rowFiniteTotalGrading_iff ℳ _).2 fun y ↦ by
        by_cases hy : y = x
        · subst hy
          simp [y.2]
        · simp [Finsupp.single_eq_of_ne hy]) ∘ₗ
    (shiftedModuleComplexXEquiv hM p n).toLinearMap

/-- `rowFiniteIndexGradedPieceSingleX` inserts an element at `x`. -/
@[simp]
theorem rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingleX
    (x : {x // ind x = p}) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n
        (rowFiniteIndexGradedPieceSingleX hM ind x n α) : {x // ind x = p} →₀ M) =
      Finsupp.single x (shiftedModuleComplexXEquiv hM p n α : M) := by
  simp only [rowFiniteIndexGradedPieceSingleX, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  -- The remaining equation holds by unfolding the corestriction of the codomain.
  rfl

/-- **The insertion at a generator** `x` of index `p`, as a morphism of complexes from
`shiftedModuleComplex hM p` to the graded piece of index `p`. -/
noncomputable def rowFiniteIndexGradedPieceSingle (x : {x // ind x = p}) :
    shiftedModuleComplex.{uR, uA, uM, uP} hM p ⟶ rowFiniteIndexGradedPieceComplex ind hM p where
  f n := ModuleCat.ofHom (rowFiniteIndexGradedPieceSingleX hM ind x n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦
      (rowFiniteIndexGradedPieceComplexXEquiv hM p (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [rowFiniteIndexGradedPieceComplexXEquiv_d,
      rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingleX,
      rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingleX,
      shiftedModuleComplexXEquiv_d,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

/-- `rowFiniteIndexGradedPieceSingle` inserts an element at `x`. -/
@[simp]
theorem rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f
    (x : {x // ind x = p}) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n
        (((rowFiniteIndexGradedPieceSingle hM ind x).f n).hom α) : {x // ind x = p} →₀ M) =
      Finsupp.single x (shiftedModuleComplexXEquiv hM p n α : M) :=
  rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingleX hM ind x n α

/-- Every element of the graded piece is the sum of the insertions of its values at the
generators of its support. -/
theorem sum_rowFiniteIndexGradedPieceSingle_f (n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n) :
    ∑ x ∈ (rowFiniteIndexGradedPieceComplexXEquiv hM p n f : {x // ind x = p} →₀ M).support,
      ((rowFiniteIndexGradedPieceSingle hM ind x).f n).hom
        ((shiftedModuleComplexXEquiv hM p n).symm
          ⟨_, rowFiniteIndexGradedPieceComplexXEquiv_apply_mem hM ind n f x⟩) = f := by
  refine (rowFiniteIndexGradedPieceComplexXEquiv hM p n).injective (Subtype.ext ?_)
  rw [map_sum, Submodule.coe_sum]
  simp only [rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f,
    LinearEquiv.apply_symm_apply]
  exact Finsupp.sum_single _

/-- Two maps out of a term of the graded piece agree when they agree after every insertion at a
generator. -/
theorem rowFiniteIndexGradedPieceComplex_hom_ext_X {n : ℤ} {N : ModuleCat.{max uP uM} R}
    {φ ψ : (rowFiniteIndexGradedPieceComplex ind hM p).X n ⟶ N}
    (h : ∀ x, (rowFiniteIndexGradedPieceSingle hM ind x).f n ≫ φ =
      (rowFiniteIndexGradedPieceSingle hM ind x).f n ≫ ψ) : φ = ψ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  rw [← sum_rowFiniteIndexGradedPieceSingle_f hM ind n f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, h x]

/-! ### The graded piece as a coproduct -/

/-- The insertions at the generators of index `p` exhibit the degree-`n` term of the graded
piece of index `p` as a coproduct of copies of `ℳ (n + p)`: a family of maps out of the copies
is summed over the finite support of a family of coefficients. -/
noncomputable def isColimitRowFiniteIndexGradedPieceCofanX (n : ℤ) :
    IsColimit (Cofan.mk ((rowFiniteIndexGradedPieceComplex ind hM p).X n)
      fun x : {x // ind x = p} ↦ (rowFiniteIndexGradedPieceSingle hM ind x).f n) :=
  Cofan.IsColimit.mk _
    (fun s ↦ ModuleCat.ofHom <|
      Finsupp.lsum R (fun x ↦ (s.inj x).hom ∘ₗ
          (shiftedModuleComplexXEquiv hM p n).symm.toLinearMap ∘ₗ
            DirectSum.component R ℤ (fun i ↦ ℳ i) (n + p) ∘ₗ
              (DirectSum.decomposeLinearEquiv ℳ).toLinearMap) ∘ₗ
        (Submodule.subtype _) ∘ₗ (rowFiniteIndexGradedPieceComplexXEquiv hM p n).toLinearMap)
    (fun s x ↦ ModuleCat.hom_ext (LinearMap.ext fun α ↦ by
      simp [rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f]))
    fun s φ hφ ↦ rowFiniteIndexGradedPieceComplex_hom_ext_X hM ind fun x ↦
      (hφ x).trans (ModuleCat.hom_ext (LinearMap.ext fun α ↦ by
        simp [rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f])).symm

/-- The graded piece of index `p`, as a cofan of copies of `shiftedModuleComplex hM p` with the
insertions at the generators of index `p`. -/
noncomputable abbrev rowFiniteIndexGradedPieceCofan :
    Cofan fun _ : {x // ind x = p} ↦ shiftedModuleComplex.{uR, uA, uM, uP} hM p :=
  Cofan.mk (rowFiniteIndexGradedPieceComplex ind hM p) (rowFiniteIndexGradedPieceSingle hM ind)

/-- **The graded piece is a coproduct.** The complex of finite-support families of coefficients
on the generators of index `p` is the coproduct, over these generators, of copies of
`shiftedModuleComplex hM p`, with the insertions at the generators. -/
noncomputable def isColimitRowFiniteIndexGradedPieceCofan :
    IsColimit (rowFiniteIndexGradedPieceCofan hM ind (p := p)) :=
  HomologicalComplex.isColimitOfEval _ _ fun n ↦
    (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval _ _ n) _ _).symm
      (isColimitRowFiniteIndexGradedPieceCofanX hM ind n)

/-! ### The cohomology of a graded piece -/

/-- The insertions at the generators of index `p` exhibit the cohomology of the graded piece of
index `p` as a coproduct of copies of the cohomology of `shiftedModuleComplex hM p`: cohomology
commutes with the coproduct `isColimitRowFiniteIndexGradedPieceCofan`, since coproducts of modules
are exact. -/
noncomputable def isColimitRowFiniteIndexGradedPieceHomologyCofan (n : ℤ) :
    IsColimit (Cofan.mk ((rowFiniteIndexGradedPieceComplex ind hM p).homology n)
      fun x : {x // ind x = p} ↦
        HomologicalComplex.homologyMap (rowFiniteIndexGradedPieceSingle hM ind x) n) :=
  haveI : AB4OfSize.{uP} (ModuleCat.{max uP uM} R) := AB4OfSize_shrink.{uP, uM} _
  isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor _ _ n) _ _
    (isColimitRowFiniteIndexGradedPieceCofan hM ind)

/-- **The cohomology of a graded piece of the row-finite index filtration**: the cohomology of
the complex of finite-support families of coefficients on the generators of index `p`, in degree
`n`, is the coproduct over these generators of the cohomology of `shiftedModuleComplex hM p` in
degree `n`, that is of `ℳ` in degree `n + p`, through the insertions at the generators. -/
noncomputable def rowFiniteIndexGradedPieceHomologyIso (n : ℤ) :
    (rowFiniteIndexGradedPieceComplex ind hM p).homology n ≅
      ∐ fun _ : {x // ind x = p} ↦ (shiftedModuleComplex.{uR, uA, uM, uP} hM p).homology n :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitRowFiniteIndexGradedPieceHomologyCofan hM ind n)).symm

/-- The inverse of `rowFiniteIndexGradedPieceHomologyIso` is, on the summand of a generator `x`,
the map in cohomology of the insertion at `x`. -/
@[reassoc (attr := simp)]
theorem ι_rowFiniteIndexGradedPieceHomologyIso_inv (n : ℤ) (x : {x // ind x = p}) :
    Sigma.ι (fun _ : {x // ind x = p} ↦ (shiftedModuleComplex.{uR, uA, uM, uP} hM p).homology n) x ≫
        (rowFiniteIndexGradedPieceHomologyIso hM ind n).inv =
      HomologicalComplex.homologyMap (rowFiniteIndexGradedPieceSingle hM ind x) n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _
    (isColimitRowFiniteIndexGradedPieceHomologyCofan hM ind n) (Discrete.mk x)

/-- On the summand of a generator `x`, `rowFiniteIndexGradedPieceHomologyIso` inverts the map in
cohomology of the insertion at `x`. -/
@[reassoc (attr := simp)]
theorem homologyMap_rowFiniteIndexGradedPieceSingle_comp_rowFiniteIndexGradedPieceHomologyIso_hom
    (n : ℤ) (x : {x // ind x = p}) :
    HomologicalComplex.homologyMap (rowFiniteIndexGradedPieceSingle hM ind x) n ≫
        (rowFiniteIndexGradedPieceHomologyIso hM ind n).hom =
      Sigma.ι (fun _ : {x // ind x = p} ↦ (shiftedModuleComplex.{uR, uA, uM, uP} hM p).homology n)
        x := by
  rw [← ι_rowFiniteIndexGradedPieceHomologyIso_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-! ### The first page of the index spectral sequence -/

namespace RowFiniteTwistingCocycle

variable {ind} (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)

/-- **The first page of the row-finite index spectral sequence as a direct sum.** Its object at
`(p, q)`, on page `2` in Mathlib's numbering, is the coproduct over the generators of index
`q + 1` of the cohomology in degree `p + q` of `shiftedModuleComplex hM (q + 1)`, that is of
copies of the cohomology of `ℳ` in degree `p + 2 q + 1`. -/
noncomputable def indexSpectralSequenceFirstPageXIsoSigma (pq : ℤ × ℤ) :
    ((m.indexSpectralSequence hM hm).page 2).X pq ≅
      ∐ fun _ : {x // ind x = pq.2 + 1} ↦
        (shiftedModuleComplex.{uR, uA, uM, uP} hM (pq.2 + 1)).homology (pq.1 + pq.2) :=
  m.indexSpectralSequenceFirstPageXIso hM hm pq ≪≫ rowFiniteIndexGradedPieceHomologyIso hM ind _

end RowFiniteTwistingCocycle

end TauCeti

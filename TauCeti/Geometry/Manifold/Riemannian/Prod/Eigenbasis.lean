/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.InnerProductSpace.L2.Product
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenbasis
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic

/-!
# The eigenfunction expansion of the Laplacian of a closed product

Let `M` and `N` be closed manifolds with smooth Riemannian metrics, and give `M × N` the product
metric. The Laplace–Beltrami operator `Δ = div grad` of the product splits as
`Δ_{M × N} = Δ_M ⊗ 1 + 1 ⊗ Δ_N` (`TauCeti.Manifold.laplaceBeltrami_prod`), so the product
`f ⊠ g : (x, y) ↦ f x * g y` of eigenfunctions `Δ f = -a f` and `Δ g = -b g` is an eigenfunction
with `Δ (f ⊠ g) = -(a + b) (f ⊠ g)`
(`TauCeti.Manifold.smoothLaplaceBeltrami_prod_mul_of_eq_neg_smul`).
This file proves that such products span every eigenspace of `Δ_{M × N}`: the eigenfunction
expansions of the factors multiply to an eigenfunction expansion of the product.

Let `uᵢ` and `vⱼ` be smooth eigenfunctions, `Δ uᵢ = -μᵢ uᵢ` and `Δ vⱼ = -νⱼ vⱼ`, whose classes form
Hilbert bases of `L²(M)` and `L²(N)`, as provided by
`TauCeti.Manifold.SobolevH1.exists_hilbertBasis_smoothLaplaceBeltrami_eq_neg_smul`.

* **The product eigenbasis.** The classes of the products `uᵢ ⊠ vⱼ` form a Hilbert basis of
  `L²(M × N)` (`TauCeti.Manifold.SobolevH1.exists_hilbertBasis_toLp_ofSmooth_prod_mul`). The
  Riemannian volume of `M × N` is the product of the volumes (`TauCeti.riemannianVolume_prod`), so
  the class of `uᵢ ⊠ vⱼ` is the pointwise product of the classes of `uᵢ` and `vⱼ`
  (`TauCeti.Manifold.SobolevH1.toLp_ofSmooth_prod_mul`), and pointwise products of Hilbert bases
  of the factors form a Hilbert basis of `L²` of the product measure (`HilbertBasis.prod`).
* **Multiplicities.** The `(-c)`-eigenspace of `Δ_{M × N}` on smooth functions has dimension the
  number of pairs `(i, j)` with `μᵢ + νⱼ = c`
  (`TauCeti.Manifold.SobolevH1.finrank_eigenspace_smoothLaplaceBeltrami_prod_eq_ncard`), and it is
  spanned by the products `uᵢ ⊠ vⱼ` with `μᵢ + νⱼ = c`
  (`TauCeti.Manifold.SobolevH1.eigenspace_smoothLaplaceBeltrami_prod_eq_span`).
* **The spectrum.** Consequently `-c` is an eigenvalue of `Δ_{M × N}` exactly when `c = a + b` for
  eigenvalues `-a` of `Δ_M` and `-b` of `Δ_N`
  (`TauCeti.Manifold.SobolevH1.hasEigenvalue_smoothLaplaceBeltrami_prod_iff`). For instance, the
  eigenvalues of `-Δ` on the circle `ℝ / 2πℤ` are the squares `k²`, so those on the flat torus
  `S¹ × S¹` are the sums `k² + l²` of two squares.

The rough Laplacian of the flat connection on the trivial line bundle is `-Δ`, so these are also the
product eigenfunction expansions of the shifted connection Laplacians `1 + ∇*∇` of trivial line
bundles, with eigenvalues `(1 + μᵢ) + (1 + νⱼ) - 1` on `M × N`.

## References

* M. Berger, P. Gauduchon, E. Mazet, *Le spectre d'une variété riemannienne*, Lecture Notes in
  Mathematics 194, Springer (1971), Chapter III (the spectrum of a Riemannian product).
-/

public section

noncomputable section

open Bundle MeasureTheory Module
open scoped ContDiff Manifold TauCeti

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- **The Laplacian of a product of smooth functions** on `M × N`, as smooth functions:
`Δ (f ⊠ g) = (Δ f) ⊠ g + f ⊠ (Δ g)`, where `f ⊠ g` is `(x, y) ↦ f x * g y`. -/
theorem smoothLaplaceBeltrami_prod_mul (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯) :
    smoothLaplaceBeltrami (I.prod J) (M × N) (f.comp ContMDiffMap.fst * g.comp ContMDiffMap.snd) =
      (smoothLaplaceBeltrami I M f).comp ContMDiffMap.fst * g.comp ContMDiffMap.snd +
        f.comp ContMDiffMap.fst * (smoothLaplaceBeltrami J N g).comp ContMDiffMap.snd := by
  ext p
  simp only [smoothLaplaceBeltrami_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_mul, Pi.add_apply,
    Pi.mul_apply, ContMDiffMap.comp_apply]
  exact laplaceBeltrami_prod_mul (f.contMDiff.of_le (by simp)).contMDiffAt
    (g.contMDiff.of_le (by simp)).contMDiffAt

/-- **A product of eigenfunctions is an eigenfunction.** If `Δ f = -a f` on `M` and `Δ g = -b g`
on `N`, then `Δ (f ⊠ g) = -(a + b) (f ⊠ g)` on `M × N`. -/
theorem smoothLaplaceBeltrami_prod_mul_of_eq_neg_smul {f : C^∞⟮I, M; ℝ⟯}
    {g : C^∞⟮J, N; ℝ⟯} {a b : ℝ} (hf : smoothLaplaceBeltrami I M f = -a • f)
    (hg : smoothLaplaceBeltrami J N g = -b • g) :
    smoothLaplaceBeltrami (I.prod J) (M × N) (f.comp ContMDiffMap.fst * g.comp ContMDiffMap.snd) =
      -(a + b) • (f.comp ContMDiffMap.fst * g.comp ContMDiffMap.snd) := by
  rw [smoothLaplaceBeltrami_prod_mul, hf, hg]
  ext p
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_mul, ContMDiffMap.coe_smul, Pi.add_apply,
    Pi.mul_apply, Pi.smul_apply, ContMDiffMap.comp_apply, smul_eq_mul]
  ring

end TauCeti.Manifold

namespace TauCeti.Manifold.SobolevH1

section Continuous

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N] [IsManifold J 1 N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y)]

/-- **The class of a product of smooth functions** in `L²(M × N)` is the pointwise product
`(x, y) ↦ f x * g y` of the classes of `f` in `L²(M)` and of `g` in `L²(N)`
(`MeasureTheory.Lp.prodMul`), read in `L²(M × N)` through the equality of the Riemannian volume of
`M × N` with the product of the volumes. -/
theorem toLp_ofSmooth_prod_mul (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯) :
    toLp (ofSmooth (f.comp ContMDiffMap.fst * g.comp ContMDiffMap.snd)) =
      castLpₗᵢ (𝕜 := ℝ) riemannianVolume_prod.symm
        (Lp.prodMul (toLp (ofSmooth f)) (toLp (ofSmooth g))) := by
  -- The two classes are compared through representatives, almost everywhere for the product of
  -- the volumes, which is the Riemannian volume of `M × N`.
  have hae : MeasureTheory.ae (riemannianVolume (I.prod J) (M × N)) =
      MeasureTheory.ae ((riemannianVolume I M).prod (riemannianVolume J N)) := by
    rw [riemannianVolume_prod]
  have hprod : ⇑(Lp.prodMul (toLp (ofSmooth f)) (toLp (ofSmooth g))) =ᵐ[(riemannianVolume I M).prod
      (riemannianVolume J N)] fun q : M × N ↦ f q.1 * g q.2 := by
    filter_upwards [Lp.coeFn_prodMul (toLp (ofSmooth f)) (toLp (ofSmooth g)),
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (toLp_ofSmooth_ae_eq f),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp (toLp_ofSmooth_ae_eq g)] with q hq hf hg
    rw [hq]
    exact congrArg₂ (· * ·) hf hg
  refine Lp.ext ((toLp_ofSmooth_ae_eq _).trans ?_)
  rw [Filter.EventuallyEq, hae]
  filter_upwards [hprod] with q hq
  rw [coeFn_castLpₗᵢ, hq]
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.comp_apply,
    ContMDiffMap.fst_apply, ContMDiffMap.snd_apply]

/-- **The product eigenbasis.** If the classes of smooth functions `uᵢ` form a Hilbert basis of
`L²(M)` and those of `vⱼ` a Hilbert basis of `L²(N)`, then the classes of the products
`(x, y) ↦ uᵢ x * vⱼ y` form a Hilbert basis of `L²(M × N)`, indexed by the pairs `(i, j)`. -/
theorem exists_hilbertBasis_toLp_ofSmooth_prod_mul {ι κ : Type*}
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (riemannianVolume I M)))
    (b' : HilbertBasis κ ℝ (Lp ℝ 2 (riemannianVolume J N))) {u : ι → C^∞⟮I, M; ℝ⟯}
    {v : κ → C^∞⟮J, N; ℝ⟯} (hu : ∀ i, toLp (ofSmooth (u i)) = b i)
    (hv : ∀ j, toLp (ofSmooth (v j)) = b' j) :
    ∃ B : HilbertBasis (ι × κ) ℝ (Lp ℝ 2 (riemannianVolume (I.prod J) (M × N))),
      ∀ ij, toLp (ofSmooth ((u ij.1).comp ContMDiffMap.fst * (v ij.2).comp ContMDiffMap.snd)) =
        B ij :=
  ⟨(b.prod b').mapₗᵢ (castLpₗᵢ riemannianVolume_prod.symm), fun ij ↦ by
    rw [HilbertBasis.mapₗᵢ_apply, HilbertBasis.prod_apply, toLp_ofSmooth_prod_mul,
      hu, hv]⟩

end Continuous

section Smooth

attribute [local instance] instIsContinuousRiemannianBundleOfContMDiffInfty

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N] [IsManifold J ∞ N]
  [T2Space N] [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {ι κ : Type*} {b : HilbertBasis ι ℝ (Lp ℝ 2 (riemannianVolume I M))}
  {b' : HilbertBasis κ ℝ (Lp ℝ 2 (riemannianVolume J N))} {u : ι → C^∞⟮I, M; ℝ⟯}
  {v : κ → C^∞⟮J, N; ℝ⟯} {μ : ι → ℝ} {ν : κ → ℝ}

/-- **Multiplicities of the eigenvalues of the Laplacian of a product.** Let the classes of smooth
functions `uᵢ` with `Δ uᵢ = -μᵢ uᵢ` form a Hilbert basis of `L²(M)`, and those of `vⱼ` with
`Δ vⱼ = -νⱼ vⱼ` a Hilbert basis of `L²(N)`. Then the `(-c)`-eigenspace of the Laplacian of `M × N`
on smooth functions has dimension the number of pairs `(i, j)` with `μᵢ + νⱼ = c`. -/
theorem finrank_eigenspace_smoothLaplaceBeltrami_prod_eq_ncard
    (hu : ∀ i, toLp (ofSmooth (u i)) = b i) (hv : ∀ j, toLp (ofSmooth (v j)) = b' j)
    (hμ : ∀ i, smoothLaplaceBeltrami I M (u i) = -μ i • u i)
    (hν : ∀ j, smoothLaplaceBeltrami J N (v j) = -ν j • v j) (c : ℝ) :
    finrank ℝ (Module.End.eigenspace (smoothLaplaceBeltrami (I.prod J) (M × N)) (-c)) =
      {ij : ι × κ | μ ij.1 + ν ij.2 = c}.ncard := by
  obtain ⟨B, hB⟩ := exists_hilbertBasis_toLp_ofSmooth_prod_mul b b' hu hv
  exact finrank_eigenspace_smoothLaplaceBeltrami_eq_ncard B hB
    (fun ij ↦ Manifold.smoothLaplaceBeltrami_prod_mul_of_eq_neg_smul (hμ ij.1)
      (hν ij.2)) c

/-- **The eigenspaces of the Laplacian of a product are spanned by products of eigenfunctions.**
Let the classes of smooth functions `uᵢ` with `Δ uᵢ = -μᵢ uᵢ` form a Hilbert basis of `L²(M)`, and
those of `vⱼ` with `Δ vⱼ = -νⱼ vⱼ` a Hilbert basis of `L²(N)`. Then the `(-c)`-eigenspace of the
Laplacian of `M × N` on smooth functions is spanned by the products `(x, y) ↦ uᵢ x * vⱼ y` with
`μᵢ + νⱼ = c`. -/
theorem eigenspace_smoothLaplaceBeltrami_prod_eq_span
    (hu : ∀ i, toLp (ofSmooth (u i)) = b i) (hv : ∀ j, toLp (ofSmooth (v j)) = b' j)
    (hμ : ∀ i, smoothLaplaceBeltrami I M (u i) = -μ i • u i)
    (hν : ∀ j, smoothLaplaceBeltrami J N (v j) = -ν j • v j) (c : ℝ) :
    Module.End.eigenspace (smoothLaplaceBeltrami (I.prod J) (M × N)) (-c) =
      Submodule.span ℝ ((fun ij : ι × κ ↦ (u ij.1).comp ContMDiffMap.fst *
        (v ij.2).comp ContMDiffMap.snd) '' {ij | μ ij.1 + ν ij.2 = c}) := by
  set S := {ij : ι × κ | μ ij.1 + ν ij.2 = c}
  set w := fun ij : ι × κ ↦ (u ij.1).comp ContMDiffMap.fst * (v ij.2).comp ContMDiffMap.snd
  set V := Module.End.eigenspace (smoothLaplaceBeltrami (I.prod J) (M × N)) (-c)
  obtain ⟨B, hB⟩ := exists_hilbertBasis_toLp_ofSmooth_prod_mul b b' hu hv
  have hmem (ij : S) : w ij ∈ V := by
    rw [Module.End.mem_eigenspace_iff, ← ij.property]
    exact Manifold.smoothLaplaceBeltrami_prod_mul_of_eq_neg_smul (hμ _) (hν _)
  -- The products are linearly independent, since their classes in `L²(M × N)` are orthonormal.
  have hli : LinearIndependent ℝ fun ij : S ↦ w ij := by
    refine LinearIndependent.of_comp
      ((toLp (I := I.prod J) (M := M × N)).toLinearMap ∘ₗ ofSmooth) ?_
    convert B.orthonormal.linearIndependent.comp ((↑) : S → ι × κ) Subtype.val_injective
    exact funext fun ij ↦ hB ij
  -- Lying in the finite-dimensional eigenspace, there are finitely many of them.
  have hfin : Finite S :=
    (LinearIndependent.of_comp V.subtype (v := fun ij : S ↦ (⟨w ij, hmem ij⟩ : V)) hli).finite
  have := Fintype.ofFinite S
  refine (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_).symm
  · rintro _ ⟨ij, hij, rfl⟩
    exact hmem ⟨ij, hij⟩
  · rw [Set.image_eq_range, finrank_span_eq_card hli,
      finrank_eigenspace_smoothLaplaceBeltrami_prod_eq_ncard hu hv hμ hν,
      Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **The spectrum of the Laplacian of a product.** `-c` is an eigenvalue of the Laplacian of
`M × N` on smooth functions exactly when `c = a + b` for an eigenvalue `-a` of the Laplacian of `M`
and an eigenvalue `-b` of the Laplacian of `N`. -/
theorem hasEigenvalue_smoothLaplaceBeltrami_prod_iff (c : ℝ) :
    Module.End.HasEigenvalue (smoothLaplaceBeltrami (I.prod J) (M × N)) (-c) ↔
      ∃ a b, Module.End.HasEigenvalue (smoothLaplaceBeltrami I M) (-a) ∧
        Module.End.HasEigenvalue (smoothLaplaceBeltrami J N) (-b) ∧ a + b = c := by
  obtain ⟨s, b, μ, u, hb, hu, hμ, -⟩ := exists_hilbertBasis_smoothLaplaceBeltrami_eq_neg_smul
    (I := I) (M := M)
  obtain ⟨t, b', ν, v, hb', hv, hν, -⟩ := exists_hilbertBasis_smoothLaplaceBeltrami_eq_neg_smul
    (I := J) (M := N)
  replace hu (i : s) : toLp (ofSmooth (u i)) = b i := by rw [hb, hu]
  replace hv (j : t) : toLp (ofSmooth (v j)) = b' j := by rw [hb', hv]
  obtain ⟨B, hB⟩ := exists_hilbertBasis_toLp_ofSmooth_prod_mul b b' hu hv
  have hB' (ij : s × t) : smoothLaplaceBeltrami (I.prod J) (M × N)
      ((u ij.1).comp ContMDiffMap.fst * (v ij.2).comp ContMDiffMap.snd) =
        -(μ ij.1 + ν ij.2) • ((u ij.1).comp ContMDiffMap.fst * (v ij.2).comp ContMDiffMap.snd) :=
    Manifold.smoothLaplaceBeltrami_prod_mul_of_eq_neg_smul (hμ _) (hν _)
  simp only [hasEigenvalue_smoothLaplaceBeltrami_iff_exists_eq B hB hB',
    hasEigenvalue_smoothLaplaceBeltrami_iff_exists_eq b hu hμ,
    hasEigenvalue_smoothLaplaceBeltrami_iff_exists_eq b' hv hν, Prod.exists]
  constructor
  · rintro ⟨i, j, rfl⟩
    exact ⟨_, _, ⟨i, rfl⟩, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨_, _, ⟨i, rfl⟩, ⟨j, rfl⟩, rfl⟩
    exact ⟨i, j, rfl⟩

end Smooth

end TauCeti.Manifold.SobolevH1

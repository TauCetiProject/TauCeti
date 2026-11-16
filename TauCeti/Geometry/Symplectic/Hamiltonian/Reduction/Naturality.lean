/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Naturality of reduced forms: maps, symmetries and products

Symplectic reduction produces a manifold `Z` with smooth maps `i : Z → M` into a manifold with a
form `σ` and `p : Z → Q` onto a manifold with a form `η`, such that `p^* η = i^* σ`. For
Marsden–Weinstein–Meyer reduction, `Z = μ⁻¹(c)`, `i` is its inclusion, `p : Z → Z / G_c` the orbit
projection and `η` the reduced symplectic form
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`). This file
proves that such data are compatible with maps and products. As there, `p` is assumed surjective
with surjective differentials (for instance a surjective submersion), which makes `p^*` injective
on forms, so that `η` is determined by `i^* σ`.

* **Maps.** Let `(i', p', η')` be data of the same kind for `(M', σ')`, and let `φZ : Z → Z'` carry
  `i^* σ` to `i'^* σ'`, that is `φZ^* (i'^* σ') = i^* σ`. This holds when `φZ` is the restriction
  of a map `φ : M → M'` with `φ^* σ' = σ` and `i' ∘ φZ = φ ∘ i`, such as a `G`-equivariant
  symplectic map, restricted to the levels. Then a map `φQ : Q → Q'` with `φQ ∘ p = p' ∘ φZ`
  pulls the reduced form back to the reduced form, `φQ^* η' = η`
  (`TauCeti.SmoothForm.mpullback_eq_of_mpullback_eq`). If `p` is a surjective submersion out of a
  boundaryless manifold and `φZ` carries the fibres of `p` into fibres of `p'`, such a smooth `φQ`
  exists and is unique (`TauCeti.SmoothForm.existsUnique_comp_eq_and_mpullback_eq`). The fibre
  condition holds when the fibres of `p` are the orbits of a group `K` and `φZ` intertwines the
  action of `K` with an action of a group `K'` over `p'`, as the restriction of an equivariant
  map to the levels intertwines the stabilizers.
* **Symmetries.** Smooth invariant maps descend: a smooth map `f` on `M` with `f ∘ i` constant on
  the fibres of `p` is `F ∘ p` on `Z` for a unique smooth `F` on `Q`
  (`Manifold.IsSubmersion.existsUnique_contMDiff_comp_eq` applied to `f ∘ i`), as in the reduction
  of Hamiltonian dynamics of `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction`. An action of a
  monoid `L` on `Z` by smooth maps preserving `i^* σ` and the fibres of `p`, such as a symmetry of
  `(M, σ)` commuting with the action of `G` and preserving `μ`, restricted to a level, descends
  to an action of `L` on `Q` by smooth maps preserving `η`
  (`TauCeti.SmoothForm.exists_comp_eq_and_mpullback_eq_of_smul`).
* **Products.** The product of the data `(i₁, p₁, η₁)` and `(i₂, p₂, η₂)` is reduction data for the
  product form: `(p₁ × p₂)^* (η₁ ⊞ η₂) = (i₁ × i₂)^* (σ₁ ⊞ σ₂)`
  (`TauCeti.SmoothTwoForm.mpullback_prodMap_prod_eq_mpullback_prodMap_prod`). So the reduced form of
  the product is the product of the reduced forms
  (`TauCeti.SmoothTwoForm.eq_prod_of_mpullback_prodMap_eq`).

No statement needs the forms to be closed or nondegenerate, nor `i` to be an immersion.

## Main results

* `TauCeti.SmoothForm.mpullback_eq_of_mpullback_eq`: maps of reduction data pull reduced forms
  back to reduced forms.
* `TauCeti.SmoothForm.existsUnique_comp_eq_and_mpullback_eq`: a fibre-preserving map of levels
  induces a unique smooth map of the reduced spaces, which pulls back the reduced form.
* `TauCeti.SmoothForm.exists_comp_eq_and_mpullback_eq_of_smul`: an action on the level preserving
  the restricted form and the fibres descends to an action on the reduced space preserving the
  reduced form.
* `TauCeti.SmoothTwoForm.mpullback_prodMap_prod_eq_mpullback_prodMap_prod`,
  `TauCeti.SmoothTwoForm.eq_prod_of_mpullback_prodMap_eq`: reduction of products.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* J.-P. Ortega, T. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics 222,
  Birkhäuser, 2004.
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M EZ HZ Z EQ HQ Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ 1 Z]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ 1 Q]
  {E' H' M' EZ' HZ' Z' EQ' HQ' Q' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [NormedAddCommGroup EZ'] [NormedSpace ℝ EZ'] [TopologicalSpace HZ']
  {IZ' : ModelWithCorners ℝ EZ' HZ'} [TopologicalSpace Z'] [ChartedSpace HZ' Z']
  [IsManifold IZ' 1 Z']
  [NormedAddCommGroup EQ'] [NormedSpace ℝ EQ'] [TopologicalSpace HQ']
  {IQ' : ModelWithCorners ℝ EQ' HQ'} [TopologicalSpace Q'] [ChartedSpace HQ' Q']
  [IsManifold IQ' 1 Q']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {σ : SmoothForm I M F k} {η : SmoothForm IQ Q F k} {i : Z → M} {p : Z → Q}
  {σ' : SmoothForm I' M' F k} {η' : SmoothForm IQ' Q' F k} {i' : Z' → M'} {p' : Z' → Q'}
  {φZ : Z → Z'}

/-- **Maps of reduction data pull reduced forms back to reduced forms.** Let `p^* η = i^* σ` and
`p'^* η' = i'^* σ'`, where `p` is surjective with surjective differentials. If `φZ : Z → Z'`
satisfies `φZ^* (i'^* σ') = i^* σ`, then every smooth `φQ : Q → Q'` with `φQ ∘ p = p' ∘ φZ`
satisfies `φQ^* η' = η`. -/
theorem mpullback_eq_of_mpullback_eq (hi : ContMDiff IZ I ∞ i) (hp : ContMDiff IZ IQ ∞ p)
    (hi' : ContMDiff IZ' I' ∞ i') (hp' : ContMDiff IZ' IQ' ∞ p')
    (hpi : mpullback p hp η = mpullback i hi σ) (hpi' : mpullback p' hp' η' = mpullback i' hi' σ')
    (hsurj : Surjective p) (hdp : ∀ z, Surjective (mfderiv IZ IQ p z))
    (hφZ : ContMDiff IZ IZ' ∞ φZ) (hφZσ : mpullback φZ hφZ (mpullback i' hi' σ') = mpullback i hi σ)
    {φQ : Q → Q'} (hφQ : ContMDiff IQ IQ' ∞ φQ) (hpφ : φQ ∘ p = p' ∘ φZ) :
    mpullback φQ hφQ η' = η := by
  refine mpullback_injective_of_surjective hp hsurj hdp ?_
  -- `p^* φQ^* η' = φZ^* p'^* η' = φZ^* i'^* σ' = i^* σ = p^* η`.
  rw [hpi, ← hφZσ, ← hpi']
  simp only [mpullback_mpullback, hpφ]

/-- **A map of levels induces a map of reduced spaces.** Let `p^* η = i^* σ` and
`p'^* η' = i'^* σ'`, where `p` is a surjective smooth submersion out of a boundaryless manifold.
If a smooth map `φZ : Z → Z'` with `φZ^* (i'^* σ') = i^* σ` carries each fibre of `p` into a fibre
of `p'`, there is a unique map `φQ : Q → Q'` with `φQ ∘ p = p' ∘ φZ`; it is smooth and satisfies
`φQ^* η' = η`. -/
theorem existsUnique_comp_eq_and_mpullback_eq [IZ.Boundaryless] (hi : ContMDiff IZ I ∞ i)
    (hp : IsSubmersion IZ IQ ∞ p) (hi' : ContMDiff IZ' I' ∞ i') (hp' : ContMDiff IZ' IQ' ∞ p')
    (hpi : mpullback p hp.contMDiff η = mpullback i hi σ)
    (hpi' : mpullback p' hp' η' = mpullback i' hi' σ') (hsurj : Surjective p)
    (hφZ : ContMDiff IZ IZ' ∞ φZ) (hφZσ : mpullback φZ hφZ (mpullback i' hi' σ') = mpullback i hi σ)
    (hfib : FactorsThrough (p' ∘ φZ) p) :
    ∃! φQ : Q → Q', φQ ∘ p = p' ∘ φZ ∧
      ∃ hφQ : ContMDiff IQ IQ' ∞ φQ, mpullback φQ hφQ η' = η := by
  obtain ⟨φQ, ⟨hφQ, hpφ⟩, -⟩ :=
    hp.existsUnique_contMDiff_comp_eq hsurj le_rfl (hp'.comp hφZ) hfib
  exact ⟨φQ, ⟨hpφ, hφQ, mpullback_eq_of_mpullback_eq hi hp.contMDiff hi' hp' hpi hpi' hsurj
      (hp.surjective_mfderiv (by simp)) hφZ hφZσ hφQ hpφ⟩,
    fun ψ hψ ↦ hsurj.injective_comp_right (hψ.1.trans hpφ.symm)⟩

/-- **Symmetries descend to the reduced space.** Let `p^* η = i^* σ`, where `p` is a surjective
smooth submersion out of a boundaryless manifold. Let a monoid `L` act on `Z` by smooth maps
preserving `i^* σ` and carrying fibres of `p` into fibres of `p`, as a symmetry of `(M, σ)`
commuting with the action of `G` and preserving `μ` acts on a level `μ⁻¹(c)` and permutes the
orbits of the stabilizer `G_c`. Then
the action descends along `p` to an action of `L` on `Q` by smooth maps preserving `η`: there are
maps `φ l : Q → Q` with `φ l ∘ p = p ∘ (l • ·)`, `φ 1 = id` and `φ (l * l') = φ l ∘ φ l'`, each
smooth with `(φ l)^* η = η`. -/
theorem exists_comp_eq_and_mpullback_eq_of_smul [IZ.Boundaryless] {L : Type*} [Monoid L]
    [MulAction L Z] (hi : ContMDiff IZ I ∞ i) (hp : IsSubmersion IZ IQ ∞ p)
    (hpi : mpullback p hp.contMDiff η = mpullback i hi σ) (hsurj : Surjective p)
    (hL : ∀ l : L, ContMDiff IZ IZ ∞ fun z : Z ↦ l • z)
    (hLσ : ∀ l : L, mpullback (fun z : Z ↦ l • z) (hL l) (mpullback i hi σ) = mpullback i hi σ)
    (hfib : ∀ l : L, FactorsThrough (fun z ↦ p (l • z)) p) :
    ∃ φ : L → Q → Q, (∀ l, φ l ∘ p = fun z ↦ p (l • z)) ∧ φ 1 = id ∧
      (∀ l l', φ (l * l') = φ l ∘ φ l') ∧ ∀ l, ∃ hφ : ContMDiff IQ IQ ∞ (φ l),
        mpullback (φ l) hφ η = η := by
  choose φ hφ using fun l : L ↦ existsUnique_comp_eq_and_mpullback_eq hi hp hi hp.contMDiff hpi
    hpi hsurj (hL l) (hLσ l) (hfib l)
  have hpφ (l : L) : φ l ∘ p = fun z ↦ p (l • z) := (hφ l).1.1
  -- The descended maps form an action of `L` on `Q`, since `p` is surjective and equivariant.
  let : SMul L Q := ⟨φ⟩
  let : MulAction L Q := hsurj.mulAction p fun l z ↦ (congrFun (hpφ l) z).symm
  exact ⟨φ, hpφ, funext (one_smul L), fun l l' ↦ funext (mul_smul l l'), fun l ↦ (hφ l).1.2⟩

end SmoothForm

namespace SmoothTwoForm

variable {E₁ H₁ M₁ EZ₁ HZ₁ Z₁ EQ₁ HQ₁ Q₁ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
  {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
  [IsManifold IZ₁ ∞ Z₁]
  [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
  {IQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  [IsManifold IQ₁ ∞ Q₁]
  {E₂ H₂ M₂ EZ₂ HZ₂ Z₂ EQ₂ HQ₂ Q₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
  {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
  [IsManifold IZ₂ ∞ Z₂]
  [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [TopologicalSpace HQ₂]
  {IQ₂ : ModelWithCorners ℝ EQ₂ HQ₂} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂]
  [IsManifold IQ₂ ∞ Q₂]
  {σ₁ : SmoothTwoForm I₁ M₁} {η₁ : SmoothTwoForm IQ₁ Q₁} {i₁ : Z₁ → M₁} {p₁ : Z₁ → Q₁}
  {σ₂ : SmoothTwoForm I₂ M₂} {η₂ : SmoothTwoForm IQ₂ Q₂} {i₂ : Z₂ → M₂} {p₂ : Z₂ → Q₂}
  (hi₁ : ContMDiff IZ₁ I₁ ∞ i₁) (hp₁ : ContMDiff IZ₁ IQ₁ ∞ p₁)
  (hi₂ : ContMDiff IZ₂ I₂ ∞ i₂) (hp₂ : ContMDiff IZ₂ IQ₂ ∞ p₂)
  (hpi₁ : SmoothForm.mpullback p₁ hp₁ η₁ = SmoothForm.mpullback i₁ hi₁ σ₁)
  (hpi₂ : SmoothForm.mpullback p₂ hp₂ η₂ = SmoothForm.mpullback i₂ hi₂ σ₂)
include hpi₁ hpi₂

/-- **The product of reduction data is reduction data for the product form.** If
`p₁^* η₁ = i₁^* σ₁` and `p₂^* η₂ = i₂^* σ₂`, then
`(p₁ × p₂)^* (η₁ ⊞ η₂) = (i₁ × i₂)^* (σ₁ ⊞ σ₂)` on `Z₁ × Z₂`. -/
theorem mpullback_prodMap_prod_eq_mpullback_prodMap_prod :
    SmoothForm.mpullback (Prod.map p₁ p₂) (hp₁.prodMap hp₂) (η₁.prod η₂) =
      SmoothForm.mpullback (Prod.map i₁ i₂) (hi₁.prodMap hi₂) (σ₁.prod σ₂) := by
  rw [mpullback_prodMap_prod hp₁ hp₂, mpullback_prodMap_prod hi₁ hi₂, hpi₁, hpi₂]

/-- **The reduced form of a product is the product of the reduced forms.** If
`p₁^* η₁ = i₁^* σ₁` and `p₂^* η₂ = i₂^* σ₂`, where `p₁` and `p₂` are surjective with surjective
differentials, then every form `η` on `Q₁ × Q₂` with `(p₁ × p₂)^* η = (i₁ × i₂)^* (σ₁ ⊞ σ₂)` is the
product form `η₁ ⊞ η₂`. -/
theorem eq_prod_of_mpullback_prodMap_eq (hsurj₁ : Surjective p₁)
    (hdp₁ : ∀ z, Surjective (mfderiv IZ₁ IQ₁ p₁ z)) (hsurj₂ : Surjective p₂)
    (hdp₂ : ∀ z, Surjective (mfderiv IZ₂ IQ₂ p₂ z)) {η : SmoothTwoForm (IQ₁.prod IQ₂) (Q₁ × Q₂)}
    (hη : SmoothForm.mpullback (Prod.map p₁ p₂) (hp₁.prodMap hp₂) η =
      SmoothForm.mpullback (Prod.map i₁ i₂) (hi₁.prodMap hi₂) (σ₁.prod σ₂)) :
    η = η₁.prod η₂ := by
  refine SmoothForm.mpullback_injective_of_surjective (hp₁.prodMap hp₂)
    (hsurj₁.prodMap hsurj₂) (fun z ↦ ?_)
    (hη.trans (mpullback_prodMap_prod_eq_mpullback_prodMap_prod hi₁ hp₁ hi₂ hp₂ hpi₁ hpi₂).symm)
  rw [mfderiv_prodMap ((hp₁ z.1).mdifferentiableAt (by simp)) ((hp₂ z.2).mdifferentiableAt
    (by simp))]
  exact (hdp₁ z.1).prodMap (hdp₂ z.2)

end SmoothTwoForm

end TauCeti

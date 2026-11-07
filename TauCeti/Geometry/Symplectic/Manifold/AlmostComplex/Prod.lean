/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-regularity block almost complex structures

On `P × M`, combine a `Cⁿ` almost complex structure on `P` with a jointly `Cⁿ` family
of almost complex structures on `T_x M`, allowed to depend on both `p` and `x`. The result
acts diagonally under the canonical product tangent identification. In particular, for
`P = ℝ × ℝ` with its standard structure, it sends `(a, b, v)` to `(-b, a, J_(s,t,x) v)`.
The order `n : ℕ∞` includes continuous structures and the smooth endpoint. The vertical
regularity is that of an endomorphism section along `P × M → M`; it does not assert an almost
complex structure on the full product tangent bundle. `familySlice` restricts it to a native
structure on `M` at each parameter. The block construction combines it with the chosen
horizontal structure. This permits time-dependent vertical structures in suspensions without
requiring
the monodromy to preserve one fixed almost complex structure.

The native finite construction has evaluation, square, downgrade, negation and ordinary-product
APIs, and preserves joint parameter dependence without derivative loss. The existing smooth
construction specializes this one at infinite order. The evaluation formula splits the quadratic
form into horizontal and vertical
terms. Compatible vertical families therefore give a compatible block structure for the
product two-form. When the vertical family also depends smoothly on a parameter, so does the
block structure (`TauCeti.SmoothAlmostComplexStructure.contMDiff_prodFamily_family`).
Equivariance under a product map reduces to equivariance of its two blocks; for a translation
and a monodromy map this is precisely the vertical seam equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (compatible almost complex structures).
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301–354 (block structures on suspensions).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ContMDiffAlmostComplexStructure

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {n : ℕ∞} (J : ContMDiffAlmostComplexStructure I n P)
  (K : ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2))
  (hK : ContMDiff (I.prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

private def prodFamilyEndomorphism (p : P × M) :
    TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p :=
  -- Product tangent fibres and the product of tangent fibres have the same model-space
  -- representation; the public evaluation lemma uses their canonical identification.
  (J.toEndomorphism p.1).prodMap (K p).toLinearMap.toContinuousLinearMap

section Family

variable {EΛ HΛ Λ : Type*} [NormedAddCommGroup EΛ] [NormedSpace ℝ EΛ] [TopologicalSpace HΛ]
  {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ] [ChartedSpace HΛ Λ]

/-- The block endomorphism preserves joint `Cⁿ` regularity in the parameter and base point. -/
private theorem contMDiff_prodFamilyEndomorphism_family
    {K : Λ → ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2)}
    (hK : ContMDiff (IΛ.prod (I.prod I')) (I'.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (IΛ.prod (I.prod I')) ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) n
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F)
        (E := fun p : P × M ↦ TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p) r.2
        (prodFamilyEndomorphism J (K r.1) r.2)) := by
  -- On total spaces, the block structure acts separately on the two tangent components.
  refine (TauCeti.contMDiff_hom_bundle_prod_iff _).2 ?_
  have hsplit := contMDiff_equivTangentBundleProd.comp
    (contMDiff_snd : ContMDiff (IΛ.prod (I.prod I').tangent) (I.prod I').tangent n
      (Prod.snd : Λ × TangentBundle (I.prod I') (P × M) → _))
  have hhorizontal := J.contMDiff_apply le_rfl (contMDiff_fst.comp
    ((contMDiff_proj (TangentSpace (I.prod I'))).comp contMDiff_snd)) hsplit.fst
  have hvertical := (hK.comp (contMDiff_fst.prodMk
    ((contMDiff_proj (TangentSpace (I.prod I'))).comp contMDiff_snd))).clm_bundle_apply
      hsplit.snd
  exact contMDiff_equivTangentBundleProd_symm.comp (hhorizontal.prodMk hvertical)

end Family

include hK in
private theorem contMDiff_prodFamilyEndomorphism :
    ContMDiff (I.prod I') ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) n
      (fun p ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F) p
        (prodFamilyEndomorphism J K p)) :=
  -- This is the case of the constant family, with parameter in `P × M` itself.
  (contMDiff_prodFamilyEndomorphism_family J (IΛ := I.prod I') (K := fun _ : P × M ↦ K)
    (hK.comp contMDiff_snd)).comp (contMDiff_id.prodMk contMDiff_id)

/-- The `Cⁿ` block structure on `P × M` with horizontal block `J` and a jointly `Cⁿ`
vertical family `K_(p,x)`. The vertical block may depend on both coordinates. -/
def prodFamily : ContMDiffAlmostComplexStructure (I.prod I') n (P × M) where
  toEndomorphism := ⟨prodFamilyEndomorphism J K, contMDiff_prodFamilyEndomorphism J K hK⟩
  square_neg := by
    intro p
    ext v
    exact Prod.ext (J.apply_apply p.1 v.1) ((K p).apply_apply v.2)

/-- A jointly `Cⁿ` vertical family gives a jointly `Cⁿ` block family as a tangent-endomorphism
section along `Λ × (P × M) → P × M`. No derivatives are lost, including at `n = 0`. -/
theorem contMDiff_prodFamily_family {EΛ HΛ Λ : Type*} [NormedAddCommGroup EΛ]
    [NormedSpace ℝ EΛ] [TopologicalSpace HΛ] {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ]
    [ChartedSpace HΛ Λ] {K : Λ → ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2)}
    (hK : ContMDiff (IΛ.prod (I.prod I')) (I'.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (IΛ.prod (I.prod I')) ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) n
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F)
        (E := fun p : P × M ↦ TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p) r.2
        ((prodFamily J (K r.1) (hK.comp (contMDiff_const.prodMk contMDiff_id))).toEndomorphism
          r.2)) :=
  contMDiff_prodFamilyEndomorphism_family J hK

/-- A block structure acts separately on the two components of a product tangent vector. -/
theorem prodFamily_apply (p : P × M) (v : TangentSpace (I.prod I') p) :
    prodFamily J K hK p v = (Manifold.tangentSpaceProdEquiv p).symm
      (J p.1 (Manifold.tangentSpaceProdEquiv p v).1,
        K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  rfl

/-- The endomorphism of the block structure is the continuous linear block map. -/
@[simp]
theorem prodFamily_toEndomorphism_apply (p : P × M) :
    (prodFamily J K hK).toEndomorphism p =
      (J.toEndomorphism p.1).prodMap (K p).toLinearMap.toContinuousLinearMap := (rfl)

/-- A domain-dependent structure over `P` restricts at each parameter to a native `Cⁿ`
structure on `M`. Its joint regularity is along `P × M → M`, not on the full tangent bundle
of `P × M`. -/
def familySlice (p : P) : ContMDiffAlmostComplexStructure I' n M where
  toEndomorphism := ⟨fun x ↦ (K (p, x)).toLinearMap.toContinuousLinearMap,
    hK.comp (contMDiff_const.prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    exact (K (p, x)).apply_apply v

omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] in
@[simp]
theorem familySlice_toEndomorphism_apply (p : P) (x : M) :
    (familySlice K hK p).toEndomorphism x =
      (K (p, x)).toLinearMap.toContinuousLinearMap := (rfl)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] in
/-- Forgetting regularity commutes with slicing a domain-dependent family. -/
@[simp]
theorem familySlice_ofLE {m : ℕ∞} (hmn : m ≤ n) (p : P) :
    (familySlice K hK p).ofLE hmn =
      familySlice K (hK.of_le (by exact_mod_cast hmn)) p := by
  ext x v
  simp only [ofLE_toEndomorphism_apply, familySlice_toEndomorphism_apply]

/-- Forgetting regularity commutes with the block construction. -/
@[simp]
theorem prodFamily_ofLE {m : ℕ∞} (hmn : m ≤ n) :
    (prodFamily J K hK).ofLE hmn =
      prodFamily (J.ofLE hmn) K (hK.of_le (by exact_mod_cast hmn)) := by
  ext p v
  rw [ofLE_apply, prodFamily_apply, prodFamily_apply, ofLE_apply]

include hK in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] in
/-- Negation preserves joint regularity for a domain-dependent almost complex structure. -/
theorem contMDiff_neg_family :
    ContMDiff (I.prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
        p.2 (-K p).toLinearMap.toContinuousLinearMap) := by
  simpa only [AlmostComplexStructure.neg_toLinearMap,
    map_neg] using hK.clm_bundle_neg

omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] in
/-- Negation commutes with restricting a domain-dependent family at a parameter. -/
@[simp]
theorem familySlice_neg (p : P) :
    familySlice (fun q ↦ -K q) (contMDiff_neg_family K hK) p =
      -(familySlice K hK p) := by
  ext x v
  simp only [neg_toEndomorphism, ContMDiffSection.coe_neg, Pi.neg_apply,
    familySlice_toEndomorphism_apply, AlmostComplexStructure.neg_toLinearMap, map_neg]

/-- Negating both blocks negates the block structure. -/
@[simp]
theorem prodFamily_neg :
    prodFamily (-J) (fun p ↦ -K p) (contMDiff_neg_family K hK) =
      -(prodFamily J K hK) := by
  ext p v
  simp only [neg_toEndomorphism, ContMDiffSection.coe_neg, Pi.neg_apply,
    prodFamily_toEndomorphism_apply, AlmostComplexStructure.neg_toLinearMap, map_neg]
  rfl

/-- The ordinary product is the domain-independent vertical special case. -/
def prod (L : ContMDiffAlmostComplexStructure I' n M) :
    ContMDiffAlmostComplexStructure (I.prod I') n (P × M) :=
  prodFamily J (fun p ↦ L.almostComplexStructureAt p.2)
    (by
      simpa only [almostComplexStructureAt_toLinearMap,
        LinearMap.toContinuousLinearMap_coe, Function.comp_def]
        using L.toEndomorphism.contMDiff.comp (contMDiff_snd (I := I)))

/-- The ordinary product acts componentwise under the canonical tangent identification. -/
@[simp]
theorem prod_apply (L : ContMDiffAlmostComplexStructure I' n M) (p : P × M)
    (v : TangentSpace (I.prod I') p) :
    prod J L p v = (Manifold.tangentSpaceProdEquiv p).symm
      (J p.1 (Manifold.tangentSpaceProdEquiv p v).1,
        L p.2 (Manifold.tangentSpaceProdEquiv p v).2) := by
  simp only [prod, prodFamily_apply, almostComplexStructureAt_apply]

/-- Forgetting regularity commutes with the ordinary product. -/
@[simp]
theorem prod_ofLE (L : ContMDiffAlmostComplexStructure I' n M) {m : ℕ∞} (hmn : m ≤ n) :
    (prod J L).ofLE hmn = prod (J.ofLE hmn) (L.ofLE hmn) := by
  ext p v
  rw [ofLE_apply, prod_apply, prod_apply, ofLE_apply, ofLE_apply]

/-- Negating both factors negates the ordinary product. -/
@[simp]
theorem prod_neg (L : ContMDiffAlmostComplexStructure I' n M) :
    prod (-J) (-L) = -(prod J L) := by
  ext p v
  simp only [neg_toEndomorphism, ContMDiffSection.coe_neg, Pi.neg_apply, neg_apply,
    prod_apply]
  simp only [Manifold.tangentSpaceProdEquiv_symm_apply]
  rfl

/-- The quadratic form of a product two-form and a block almost complex structure is the sum
of its horizontal and vertical quadratic forms. -/
theorem eval₂_prod_prodFamily (σ : SmoothTwoForm I P) (τ : SmoothTwoForm I' M)
    (p : P × M) (v : TangentSpace (I.prod I') p) :
    (σ.prod τ).eval₂ p v (prodFamily J K hK p v) =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (J p.1 (Manifold.tangentSpaceProdEquiv p v).1) +
      τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  rw [SmoothTwoForm.eval₂_prod, prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- A product map intertwines the block structure at a point precisely when its horizontal
differential intertwines `J` and its vertical differential intertwines the corresponding
members of `K`. In a suspension the second condition is the seam equation. -/
theorem mfderiv_prodMap_prodFamily_iff {f : P → P} {g : M → M} (p : P × M)
    (hf : MDifferentiableAt I I f p.1) (hg : MDifferentiableAt I' I' g p.2) :
    (∀ v : TangentSpace (I.prod I') p,
      mfderiv (I.prod I') (I.prod I') (Prod.map f g) p (prodFamily J K hK p v) =
        prodFamily J K hK (f p.1, g p.2)
          (mfderiv (I.prod I') (I.prod I') (Prod.map f g) p v)) ↔
      (∀ u : TangentSpace I p.1,
        mfderiv I I f p.1 (J p.1 u) = J (f p.1) (mfderiv I I f p.1 u)) ∧
      (∀ w : TangentSpace I' p.2,
        mfderiv I' I' g p.2 (K p w) = K (f p.1, g p.2) (mfderiv I' I' g p.2 w)) := by
  constructor
  · intro h
    constructor
    · intro u
      have hu := h ((Manifold.tangentSpaceProdEquiv p).symm (u, 0))
      simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
        Manifold.mfderiv_prodMap_apply hf hg] at hu
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (fun v ↦ (Manifold.tangentSpaceProdEquiv (f p.1, g p.2) v).1) hu
    · intro w
      have hw := h ((Manifold.tangentSpaceProdEquiv p).symm (0, w))
      simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
        Manifold.mfderiv_prodMap_apply hf hg] at hw
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (fun v ↦ (Manifold.tangentSpaceProdEquiv (f p.1, g p.2) v).2) hw
  · rintro ⟨hfJ, hgK⟩ v
    obtain ⟨v, rfl⟩ := (Manifold.tangentSpaceProdEquiv p).symm.surjective v
    simp only [prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply,
      Manifold.mfderiv_prodMap_apply hf hg]
    exact congrArg (Manifold.tangentSpaceProdEquiv (f p.1, g p.2)).symm
      (Prod.ext (hfJ v.1) (hgK v.2))

end TauCeti.ContMDiffAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  (J : SmoothAlmostComplexStructure I P)
  (K : ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2))
  (hK : ContMDiff (I.prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

/-- The smooth block structure, obtained from the native finite-regularity construction at
infinite order. The vertical block may depend jointly on the domain and target point. -/
def prodFamily : SmoothAlmostComplexStructure (I.prod I') (P × M) :=
  (ContMDiffAlmostComplexStructure.prodFamily (J.toContMDiff ⊤) K hK).toSmooth

/-- Jointly smooth vertical families give jointly smooth block structures. -/
theorem contMDiff_prodFamily_family {EΛ HΛ Λ : Type*} [NormedAddCommGroup EΛ]
    [NormedSpace ℝ EΛ] [TopologicalSpace HΛ] {IΛ : ModelWithCorners ℝ EΛ HΛ} [TopologicalSpace Λ]
    [ChartedSpace HΛ Λ] {K : Λ → ∀ p : P × M, AlmostComplexStructure (TangentSpace I' p.2)}
    (hK : ContMDiff (IΛ.prod (I.prod I')) (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
        r.2.2 (K r.1 r.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (IΛ.prod (I.prod I')) ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) ∞
      (fun r : Λ × (P × M) ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F)
        (E := fun p : P × M ↦ TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p) r.2
        ((prodFamily J (K r.1) (hK.comp (contMDiff_const.prodMk contMDiff_id))).toEndomorphism
          r.2)) :=
  by
  simpa only [prodFamily, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism] using
    ContMDiffAlmostComplexStructure.contMDiff_prodFamily_family (J.toContMDiff ⊤) hK

/-- A smooth block structure acts separately on the two tangent components. -/
@[simp]
theorem prodFamily_apply (p : P × M) (v : TangentSpace (I.prod I') p) :
    prodFamily J K hK p v = (Manifold.tangentSpaceProdEquiv p).symm
      (J p.1 (Manifold.tangentSpaceProdEquiv p v).1,
        K p (Manifold.tangentSpaceProdEquiv p v).2) :=
  by
  simpa only [prodFamily, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism,
    toContMDiff_toEndomorphism_apply] using
    ContMDiffAlmostComplexStructure.prodFamily_apply (J.toContMDiff ⊤) K hK p v

/-- Viewing the smooth block construction at finite regularity gives the native finite block
construction. This includes the infinite-order equivalence with the smooth carrier. -/
@[simp]
theorem prodFamily_toContMDiff (n : ℕ∞) :
    (prodFamily J K hK).toContMDiff n =
      ContMDiffAlmostComplexStructure.prodFamily (J.toContMDiff n) K
        (hK.of_le (by simp)) := by
  ext p v
  simp only [toContMDiff_apply, prodFamily_apply,
    ContMDiffAlmostComplexStructure.prodFamily_apply]

/-- The quadratic form of a product two-form and a block almost complex structure is the sum
of its horizontal and vertical quadratic forms. -/
theorem eval₂_prod_prodFamily (σ : SmoothTwoForm I P) (τ : SmoothTwoForm I' M)
    (p : P × M) (v : TangentSpace (I.prod I') p) :
    (σ.prod τ).eval₂ p v (prodFamily J K hK p v) =
      σ.eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (J p.1 (Manifold.tangentSpaceProdEquiv p v).1) +
      τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
        (K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  simpa only [prodFamily, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism,
    toContMDiff_toEndomorphism_apply] using
    ContMDiffAlmostComplexStructure.eval₂_prod_prodFamily (J.toContMDiff ⊤) K hK σ τ p v

/-- If each block is tamed by its factor two-form, the block structure is tamed by the
product form. -/
theorem tames_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Tames J)
    (hτ : ∀ (p : P × M) (v : TangentSpace I' p.2), v ≠ 0 →
      0 < τ.eval₂ p.2 v (K p v)) :
    (σ.prod τ).Tames (prodFamily J K hK) := by
  rw [SmoothTwoForm.tames_iff]
  intro p v hv
  -- Vertical tameness at `p` makes the fibre form a linear symplectic form.
  have hτalt := SmoothForm.isAlt_bilinFormAt τ p.2
  let ωτ : SymplecticForm (TangentSpace I' p.2) :=
    { toBilinForm := τ.bilinFormAt p.2
      isAlt := hτalt
      nondegenerate := hτalt.isRefl.nondegenerate_iff_separatingLeft.2 fun w hw ↦ by
        by_contra hw0
        exact (hτ p w hw0).ne' (by simpa only [SmoothForm.bilinFormAt_apply] using hw (K p w)) }
  have hωτ : ωτ.Tames (K p) := fun w hw ↦ by
    simpa only [ωτ, SmoothForm.bilinFormAt_apply] using hτ p w hw
  have h := SymplecticForm.prod_tames (hσ.isNondegenerate.tames_iff.1 hσ p.1) hωτ
    (Manifold.tangentSpaceProdEquiv p v) ((Manifold.tangentSpaceProdEquiv p).map_ne_zero_iff.2 hv)
  rw [SymplecticForm.prod_apply_prod_self] at h
  rw [eval₂_prod_prodFamily]
  simpa only [ωτ, SmoothForm.bilinFormAt_apply,
    SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using h

/-- Invariance of each block gives invariance of the product form. -/
theorem invariant_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Invariant J)
    (hτ : ∀ (p : P × M) (v w : TangentSpace I' p.2),
      τ.eval₂ p.2 (K p v) (K p w) = τ.eval₂ p.2 v w) :
    (σ.prod τ).Invariant (prodFamily J K hK) := by
  rw [SmoothTwoForm.invariant_iff] at hσ ⊢
  intro p v w
  simp only [SmoothTwoForm.eval₂_prod, prodFamily_apply,
    ContinuousLinearEquiv.apply_symm_apply, hσ p.1, hτ p]

/-- Compatible vertical families and a compatible horizontal block give a block structure
compatible with the product two-form. -/
theorem compatible_prodFamily {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
    (hσ : σ.Compatible J) (hτ : τ.IsNondegenerate)
    (hcompat : ∀ p : P × M, (hτ.symplecticFormAt p.2).Compatible (K p)) :
    (σ.prod τ).Compatible (prodFamily J K hK) := by
  refine ⟨invariant_prodFamily J K hK hσ.invariant ?_,
    tames_prodFamily J K hK hσ.tames ?_⟩
  · intro p v w
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
      (hcompat p).invariant_apply v w
  · intro p v hv
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
      (hcompat p).tames v hv

/-- A product map intertwines the block structure at a point precisely when its horizontal
differential intertwines `J` and its vertical differential intertwines the corresponding
members of `K`. In a suspension the second condition is the seam equation. -/
theorem mfderiv_prodMap_prodFamily_iff {f : P → P} {g : M → M} (p : P × M)
    (hf : MDifferentiableAt I I f p.1) (hg : MDifferentiableAt I' I' g p.2) :
    (∀ v : TangentSpace (I.prod I') p,
      mfderiv (I.prod I') (I.prod I') (Prod.map f g) p (prodFamily J K hK p v) =
        prodFamily J K hK (f p.1, g p.2)
          (mfderiv (I.prod I') (I.prod I') (Prod.map f g) p v)) ↔
      (∀ u : TangentSpace I p.1,
        mfderiv I I f p.1 (J p.1 u) = J (f p.1) (mfderiv I I f p.1 u)) ∧
      (∀ w : TangentSpace I' p.2,
        mfderiv I' I' g p.2 (K p w) = K (f p.1, g p.2) (mfderiv I' I' g p.2 w)) := by
  simpa only [prodFamily, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism,
    toContMDiff_toEndomorphism_apply] using
    ContMDiffAlmostComplexStructure.mfderiv_prodMap_prodFamily_iff
      (J.toContMDiff ⊤) K hK p hf hg

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {F H' M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I' p.2))
  (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I') (I'.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I' x →L[ℝ] TangentSpace I' x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

/-- For the standard horizontal block `J∂s = ∂t`, `J∂t = -∂s`, the quadratic form of
`ds ∧ dt + τ` is `a² + b² + τ(v, K v)`. The vertical family is arbitrary and may depend on
both time coordinates. -/
theorem eval₂_prod_prodFamily_standard (τ : SmoothTwoForm I' M) (p : (ℝ × ℝ) × M)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I') p) :
    ((stdSymplecticForm (V := ℝ)).constSmooth.prod τ).eval₂ p v
        (prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK p v) =
      (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).1 ^ 2 +
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1).2 ^ 2 +
        τ.eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (K p (Manifold.tangentSpaceProdEquiv p v).2) := by
  rw [eval₂_prod_prodFamily, SymplecticForm.fromTangentSpace_constSmooth_apply,
    AlmostComplexStructure.fromTangentSpace_constSmooth_apply, stdSymplecticForm_apply_product_self]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Under a translation of the time plane and a fibre diffeomorphism `g`, the standard block
structure is invariant exactly when its vertical family obeys the seam equation. Taking
`c = (0, 1)` and `g = φ.symm` gives the mapping-torus deck generator; taking `c = (1, 0)` and
`g = Diffeomorph.refl I' M ∞` gives the other time-circle generator. -/
theorem mfderiv_translation_prodFamily_iff (c : ℝ × ℝ) (g : M ≃ₘ⟮I', I'⟯ M)
    (p : (ℝ × ℝ) × M) :
    (∀ v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I') p,
      mfderiv (𝓘(ℝ, ℝ × ℝ).prod I') (𝓘(ℝ, ℝ × ℝ).prod I')
          (Prod.map (fun q ↦ q + c) g) p
          (prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK p v) =
        prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK (p.1 + c, g p.2)
          (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I') (𝓘(ℝ, ℝ × ℝ).prod I')
            (Prod.map (fun q ↦ q + c) g) p v)) ↔
      ∀ w : TangentSpace I' p.2,
        mfderiv I' I' g p.2 (K p w) = K (p.1 + c, g p.2) (mfderiv I' I' g p.2 w) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1 :=
    (differentiableAt_id.add_const c).mdifferentiableAt
  rw [mfderiv_prodMap_prodFamily_iff _ _ _ _ hf (g.mdifferentiable (by simp) p.2)]
  have hhorizontal : ∀ u : TangentSpace 𝓘(ℝ, ℝ × ℝ) p.1,
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1
          ((AlmostComplexStructure.product ℝ).constSmooth p.1 u) =
        (AlmostComplexStructure.product ℝ).constSmooth (p.1 + c)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun q ↦ q + c) p.1 u) := by
    intro u
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (p.1 + c)).injective
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply,
      AlmostComplexStructure.fromTangentSpace_constSmooth_apply]
  exact and_iff_right hhorizontal

end TauCeti.SmoothAlmostComplexStructure

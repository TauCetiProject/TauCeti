/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Projective
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.Topology.Homeomorph.Prod

/-!
# Living over the fundamental class of a product base

Let `M` be an oriented `d`-manifold and `x ∈ M`. The local orientation `o x` generates the local
homology `H_d(M, M ∖ {x}; ℤ)`, which vanishes in all other degrees. By the relative Künneth theorem
the relative cross product with `o x` is therefore an isomorphism

`H_q(Y; ℤ) ≃ₗ[ℤ] H_{d + q}(M × Y, (M ∖ {x}) × Y; ℤ ⊗ ℤ)`

for every space `Y` (`TauCeti.HomologicalOrientation.singularHomologyCrossRelEquiv`), the
suspension isomorphism of local homology.

Its application is a criterion for classes over a product base. Let `p : X → Q` be a map whose
fibre `F` over `b` is closed and let `M` be compact. The cross product `[M] × α` of the fundamental
class with `α ∈ Hₖ(X; ℤ)` lives over the fundamental class at `(b', b)` for
`id × p : M × X → M × Q` exactly when `α` lives over the fundamental class at `b` for `p`
(`livesOverFundamentalClass_prodMap_singularHomologyCross_fundamentalClass_iff`).
The localization of `[M] × α` at the fibre `{b'} × F` is the image of the relative cross product
`o b' × α` in the homology of `M × X` relative to the complement of `{b'} × F`, which is the union
of `(M ∖ {b'}) × X` and `M × (X ∖ F)`. If that image vanishes, the long exact sequence of a triple
and excision write `o b' × α` as the image of a class of `(M × (X ∖ F), (M ∖ {b'}) × (X ∖ F))`
(`TopPair.exists_singularHomologyMap_excisionMap_eq`). By the suspension isomorphism that class is
`o b' × w`, so `α` comes from `X ∖ F` and its localization at `F` vanishes.

For `X = Map(S², M')` and evaluation at a point, this shows that products with a compact oriented
manifold preserve abundance with 2-spheres (`TauCeti.AlgebraicTopology.Sphere.Abundant.Prod`).

## Main definitions

* `TauCeti.HomologicalOrientation.singularHomologyCrossRelEquiv`: the suspension isomorphism
  `H_q(Y) ≃ₗ[ℤ] H_{d + q}(M × Y, (M ∖ {x}) × Y)`, `w ↦ o x × w`.

## Main results

* `livesOverFundamentalClass_prodMap_singularHomologyCross_fundamentalClass_iff`:
  `[M] × α` lives over the fundamental class for `id × p` exactly when `α` does for `p`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative Künneth formula.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 2.3 and Proposition 6.13.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Set Topology Module

namespace TauCeti

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ} (o : HomologicalOrientation M E d)
  (hd : finrank ℝ E = d) (x : M) (Y : Type) [TopologicalSpace Y]

include o hd in
/-- Since the local homology of `M` at `x` vanishes outside degree `d`, the summand
`H_d(M, M ∖ {x}) ⊗ H_q(Y)` is all of the degree `d + q` part of the tensor product of the
homologies. -/
private theorem isIso_ιTensorObj_localHomology (q : ℕ) :
    IsIso (GradedObject.Monoidal.ιTensorObj
      (fun p ↦ (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p)
      (fun q ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of Y)) d q (d + q) rfl) :=
  ⟨GradedObject.Monoidal.tensorObjDesc fun p q' h ↦
      if hp : p = d then eqToHom (by rw [hp, show q' = q by omega]) else 0,
    by simp, GradedObject.Monoidal.tensorObj_ext _ _ fun p q' h ↦ by
      by_cases hp : p = d
      · obtain rfl := hp
        obtain rfl : q' = q := by omega
        simp
      · exact ((tensorRight _).map_isZero (isZero_singularHomology_complSingleton_of_ne
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (chartAt E x) (mem_chart_source E x) hd hp)).eq_of_src
            _ _⟩

/-- **Suspension by a local orientation.** For an oriented `d`-manifold `M`, a point `x` and a
space `Y`, the relative cross product with the local orientation `o x` is an isomorphism
`H_q(Y; ℤ) ≃ₗ[ℤ] H_{d + q}(M × Y, (M ∖ {x}) × Y; ℤ ⊗ ℤ)`
(`TauCeti.HomologicalOrientation.singularHomologyCrossRelEquiv_apply`). -/
def singularHomologyCrossRelEquiv (q : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of Y)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) q :
      ModuleCat.{0} ℤ) ≃ₗ[ℤ]
      ((TopPair.ofSubset ((Prod.fst ⁻¹' {x})ᶜ : Set (TopCat.of (M × Y)))).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) (d + q) :
          ModuleCat.{0} ℤ) :=
  have (p : ℕ) : Module.Projective ℤ (localHomology (A := ModuleCat.{0} ℤ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set M) p) :=
    have := projective_singularHomology_complSingleton (ModuleCat.of ℤ (ULift.{0} ℤ)) (chartAt E x)
      (mem_chart_source E x) p
    ModuleCat.projective_of_module_projective _
  have := o.isIso_ιTensorObj_localHomology hd x Y q
  have : IsIso (TopCat.singularHomologyKunnethRel (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + q)) :=
    (TopCat.isIso_singularHomologyKunnethRel_iff (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + q)).2
      (HomologicalComplex.isIso_homologyKunneth_of_projective _ _ _)
  (TensorProduct.lid ℤ _).symm ≪≫ₗ
    TensorProduct.congr (o.localOrientationEquiv hd x) (LinearEquiv.refl ℤ _) ≪≫ₗ
    (asIso (GradedObject.Monoidal.ιTensorObj _ _ d q (d + q) rfl ≫
      TopCat.singularHomologyKunnethRel (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + q))).toLinearEquiv

/-- The suspension isomorphism sends a class `w` to the relative cross product of the local
orientation `o x` with `w`. -/
@[simp]
theorem singularHomologyCrossRelEquiv_apply (q : ℕ)
    (w : ((TopCat.toSSet.obj (TopCat.of Y)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) q :
      ModuleCat.{0} ℤ)) :
    o.singularHomologyCrossRelEquiv hd x Y q w =
      (TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d q (d + q) rfl).hom
          ((o x).val ⊗ₜ w) := by
  rw [singularHomologyCrossRelEquiv]
  -- The composite equivalence acts on the carriers of `ModuleCat` objects, whose module structures
  -- `rw` does not match against those of `LinearEquiv.trans_apply`.
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    localOrientationEquiv_apply, one_smul]
  exact ConcreteCategory.congr_hom (TopCat.ι_singularHomologyKunnethRel (TopCat.of M) (TopCat.of Y)
    ({x}ᶜ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + q) d q rfl) _

variable {X Q : Type} [TopologicalSpace X]

omit [T2Space M] in
/-- `(M ∖ {b'}) × X` lies in the complement of the fibre `{b'} × p⁻¹(b)` of `id × p`. -/
private theorem mapsTo_preimage_fst_compl_fiber (p : X → Q) (b' : M) (b : Q) :
    Set.MapsTo (𝟙 (TopCat.of (M × X))) (Prod.fst ⁻¹' ({b'}ᶜ : Set M))
      ((Prod.map id p) ⁻¹' {(b', b)})ᶜ :=
  fun _ hz hz' ↦ hz (congrArg Prod.fst hz')

omit [T2Space M] in
/-- `(M ∖ {b'}) × X` lies in its union with `M × (X ∖ p⁻¹(b))`. -/
private theorem mapsTo_preimage_fst_union (p : X → Q) (b' : M) (b : Q) :
    Set.MapsTo (𝟙 (TopCat.of (M × X))) (Prod.fst ⁻¹' ({b'}ᶜ : Set M))
      (Prod.fst ⁻¹' ({b'}ᶜ : Set M) ∪ Prod.snd ⁻¹' (p ⁻¹' {b})ᶜ) :=
  fun _ hz ↦ Or.inl hz

include hd in
/-- Localizing the cross product `[M] × α` at the fibre over `(b', b)` of `id × p : M × X → M × Q`
is the relative cross product `o b' × α ∈ H(M × X, (M ∖ {b'}) × X)` followed by the map to the
homology of `M × X` relative to the complement of that fibre. -/
private theorem fiberLocalization_prodMap_singularHomologyCross [CompactSpace M] (p : X → Q)
    (b' : M) (b : Q) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)) :
    (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
        (Prod.map id p) (b', b) (d + k)).hom
        ((TopCat.singularHomologyCross (TopCat.of M) (TopCat.of X) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom (o.fundamentalClass hd ⊗ₜ α)) =
      (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of (M × X))) (mapsTo_preimage_fst_compl_fiber p b' b))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of X) ({b'}ᶜ)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
            ((o b').val ⊗ₜ α)) := by
  have h₁ := fiberLocalization_singularHomologyCross_tmul (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (id : M → M) b' rfl (o.fundamentalClass hd) α
  rw [o.fiberLocalization_id_fundamentalClass hd] at h₁
  have h₂ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
      (mapsTo_preimage_fst_compl_fiber p b' b) (d + k))
    ((TopCat.singularHomologyCross (TopCat.of M) (TopCat.of X) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom (o.fundamentalClass hd ⊗ₜ α))
  -- The subspaces `(id ∘ fst)⁻¹' {b'}ᶜ` and `fst⁻¹' {b'}ᶜ` of `M × X` agree definitionally.
  exact h₂.symm.trans (congrArg _ h₁)

/-- **Naturality of the relative cross product with `o x` along a subspace inclusion.** For a
subset `S` of `Y` with inclusion `ι`, the relative cross product of `o x` with `ι_* w` is the image
of the relative cross product of `o x` with `w` under `id × ι`. -/
private theorem singularHomologyCrossRel_tmul_homologyMap_map (S : Set (TopCat.of Y)) {k : ℕ}
    (w : ((TopCat.toSSet.obj (TopCat.of S)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)) :
    (TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
        ((o x).val ⊗ₜ (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset S).map)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom w) =
      (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of M) ⊗ₘ (TopPair.ofSubset S).map)
        (TopCat.mapsTo_tensorHom_preimage_fst _ _ (TopCat.mapsTo_id_compl subset_rfl)))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of S) ({x}ᶜ)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
            ((o x).val ⊗ₜ w)) := by
  have h := ConcreteCategory.congr_hom (TopCat.singularHomologyCrossRel_naturality (TopCat.of M)
    (TopCat.of S) ({x}ᶜ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k)
    rfl (𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl subset_rfl) (TopPair.ofSubset S).map)
      ((o x).val ⊗ₜ w)
  have hid : (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M))
      (TopCat.mapsTo_id_compl subset_rfl)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d).hom
        (o x).val = (o x).val := by
    rw [TopPair.ofSubsetMap_id, TopPair.singularHomologyMap_id, ModuleCat.id_apply]
  -- The left side of `h` is the relative cross product of `id_* (o x)` and `ι_* w`, by definition
  -- of the composite and of the tensor product of maps in `ModuleCat`.
  exact (congrArg (fun t ↦ (TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of Y) ({x}ᶜ)
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
      (t ⊗ₜ (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset S).map)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom w)) hid.symm).trans h

/-- The map of pairs `(M × (X ∖ F), (M ∖ {b'}) × (X ∖ F)) ⟶ (M × X, (M ∖ {b'}) × X)`, for the
fibre `F = p⁻¹(b)`. -/
private abbrev prodComplPairMap (p : X → Q) (b' : M) (b : Q) :=
  TopPair.ofSubsetMap (𝟙 (TopCat.of M) ⊗ₘ (TopPair.ofSubset
    ((p ⁻¹' {b})ᶜ : Set (TopCat.of X))).map)
      (TopCat.mapsTo_tensorHom_preimage_fst _ _
        (TopCat.mapsTo_id_compl (subset_refl ({b'} : Set (TopCat.of M)))))

omit [T2Space M] in
/-- A class of `H(M × X, (M ∖ {b'}) × X)` vanishing modulo the complement of `{b'} × p⁻¹(b)`
vanishes modulo `(M ∖ {b'}) × X ∪ M × (X ∖ p⁻¹(b))`, which is that complement. -/
private theorem singularHomologyMap_union_eq_zero (p : X → Q) (b' : M) (b : Q) {j : ℕ}
    {y : ((TopPair.ofSubset (Prod.fst ⁻¹' ({b'}ᶜ : Set M) :
      Set (TopCat.of (M × X)))).singularHomology
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j : ModuleCat.{0} ℤ)}
    (hy : (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j).hom y = 0) :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_union p b' b))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j).hom y = 0 := by
  have hCUV : Set.MapsTo (𝟙 (TopCat.of (M × X))) ((Prod.map id p) ⁻¹' {(b', b)})ᶜ
      (Prod.fst ⁻¹' ({b'}ᶜ : Set M) ∪ Prod.snd ⁻¹' (p ⁻¹' {b})ᶜ) := fun z hz ↦ by
    by_contra hz'
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      not_or, not_not] at hz'
    exact hz (Prod.ext hz'.1 hz'.2)
  have hcomp : TopPair.singularHomologyMap
      (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_union p b' b))
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j =
      TopPair.singularHomologyMap
          (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b))
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hCUV)
            (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j := by
    rw [← TopPair.singularHomologyMap_comp,
      TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (mapsTo_preimage_fst_union p b' b)
        (Category.comp_id _)]
  exact (ConcreteCategory.congr_hom hcomp _).trans ((congrArg (TopPair.singularHomologyMap
    (TopPair.ofSubsetMap _ hCUV)
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) j).hom hy).trans (map_zero _))

include hd in
/-- **A relative cross product vanishing at the fibre comes from the complement.** If the image
of `y ∈ H_{d + k}(M × X, (M ∖ {b'}) × X)` modulo the complement of `{b'} × F`, `F = p⁻¹(b)`,
vanishes, then `y = o b' × ι_* w` for a class `w` of `X ∖ F` with inclusion `ι`: excision and
the long exact sequence of a triple write `y` as the image of a class of
`(M × (X ∖ F), (M ∖ {b'}) × (X ∖ F))`, which is `o b' × w` by the suspension isomorphism. -/
private theorem exists_singularHomologyCrossRel_eq (p : X → Q) (b' : M) (b : Q)
    (hF : IsClosed (p ⁻¹' {b})) {k : ℕ}
    {y : ((TopPair.ofSubset (Prod.fst ⁻¹' ({b'}ᶜ : Set M) :
      Set (TopCat.of (M × X)))).singularHomology
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k) : ModuleCat.{0} ℤ)}
    (hy : (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom y = 0) :
    ∃ w : ((TopCat.toSSet.obj (TopCat.of ↥((p ⁻¹' {b})ᶜ))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ),
      (TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of X) ({b'}ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
          ((o b').val ⊗ₜ (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset
            ((p ⁻¹' {b})ᶜ : Set (TopCat.of X))).map) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom w) =
        y := by
  obtain ⟨z, hz⟩ := TopPair.exists_singularHomologyMap_excisionMap_eq
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
    (isOpen_compl_singleton.preimage continuous_fst) (hF.isOpen_compl.preimage continuous_snd)
    (mapsTo_preimage_fst_union p b' b) (d + k) (singularHomologyMap_union_eq_zero p b' b hy)
  -- Carry `z` to `(M × (X ∖ F), (M ∖ {b'}) × (X ∖ F))` and write it as `o b' × w`.
  let φ := TopPair.ofSubsetMap (Y := TopCat.of (M × ↥((p ⁻¹' {b})ᶜ)))
    (B := (Subtype.val ⁻¹' (Prod.fst ⁻¹' ({b'}ᶜ : Set M)) :
      Set ↥(Prod.snd ⁻¹' (p ⁻¹' {b})ᶜ : Set (M × X))))
    (B' := Prod.fst ⁻¹' ({b'}ᶜ : Set M))
    (TopCat.ofHom ⟨Homeomorph.Set.preimageSnd (X := M) (p ⁻¹' {b})ᶜ,
      (Homeomorph.Set.preimageSnd (X := M) (p ⁻¹' {b})ᶜ).continuous⟩) fun _ hz ↦ hz
  have hφψ : φ ≫ prodComplPairMap p b' b = TopPair.excisionMap (X := TopCat.of (M × X))
      (Prod.snd ⁻¹' (p ⁻¹' {b})ᶜ) (Prod.fst ⁻¹' ({b'}ᶜ : Set M)) :=
    TopPair.hom_ext_of_fst _ (by
      ext z
      -- `Hom.fst (φ ≫ ψ)` does not match `TopPair.Hom.fst_comp` syntactically, since the target
      -- of `φ ≫ ψ` is written through the projection of `M ⊗ X`; it is applied factor by factor.
      change TopPair.Hom.fst (prodComplPairMap p b' b) (TopPair.Hom.fst φ z) = _
      erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
        TopPair.excisionMap_fst_apply]
      rfl)
  have hexc := (congrArg (TopPair.singularHomologyMap ·
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)) hφψ).symm.trans
    (TopPair.singularHomologyMap_comp φ _ (prodComplPairMap p b' b) (d + k))
  obtain ⟨w, hw⟩ := (o.singularHomologyCrossRelEquiv hd b' (↥((p ⁻¹' {b})ᶜ)) k).surjective
    ((TopPair.singularHomologyMap φ
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom z)
  rw [singularHomologyCrossRelEquiv_apply] at hw
  exact ⟨w, (o.singularHomologyCrossRel_tmul_homologyMap_map b' X _ w).trans
    ((congrArg (TopPair.singularHomologyMap (prodComplPairMap p b' b)
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
      hw).trans ((ConcreteCategory.congr_hom hexc z).symm.trans hz))⟩

/-- **A relative cross product with a class from the complement vanishes at the fibre.** The image
of `o b' × ι_* w`, for a class `w` of `X ∖ F` with inclusion `ι`, modulo the complement of
`{b'} × F` vanishes, since `M × (X ∖ F)` lies in that complement. -/
private theorem singularHomologyMap_singularHomologyCrossRel_homologyMap_eq_zero (p : X → Q)
    (b' : M) (b : Q) {k : ℕ}
    (w : ((TopCat.toSSet.obj (TopCat.of ↥((p ⁻¹' {b})ᶜ))).homology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)) :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
      ((TopCat.singularHomologyCrossRel (TopCat.of M) (TopCat.of X) ({b'}ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
          ((o b').val ⊗ₜ (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset
            ((p ⁻¹' {b})ᶜ : Set (TopCat.of X))).map) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom w)) =
      0 := by
  have hzero : TopPair.singularHomologyMap (prodComplPairMap p b' b)
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k) ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b)) _ (d + k) = 0 :=
    (TopPair.singularHomologyMap_comp _ _
      (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b)) (d + k)).symm.trans
      (TopPair.singularHomologyMap_eq_zero_of_fac (prodComplPairMap p b' b ≫
        TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_fiber p b' b)) _
        (TopCat.ofHom ⟨fun z : M × ↥((p ⁻¹' {b})ᶜ) ↦
          (⟨(z.1, z.2.val), fun hz ↦ z.2.property (congrArg Prod.snd hz)⟩ :
            ↥(((Prod.map id p) ⁻¹' {(b', b)})ᶜ : Set (M × X))), by fun_prop⟩)
        (by
          ext z
          -- The composite is written through the projection of `M ⊗ X`, so `rw` does not see it.
          erw [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst]
          rfl) _)
  refine (congrArg _ (o.singularHomologyCrossRel_tmul_homologyMap_map b' X _ w)).trans ?_
  exact (ConcreteCategory.congr_hom hzero _).trans (LinearMap.zero_apply _)

include hd in
/-- **Cross products with the fundamental class over a product base.** Let `M` be a compact
oriented `d`-manifold, `p : X → Q` a map whose fibre `p⁻¹(b)` is closed, and `α ∈ Hₖ(X; ℤ)`.
Then the cross product `[M] × α ∈ H_{d + k}(M × X; ℤ ⊗ ℤ)` lives over the fundamental class at
`(b', b)` for `id × p : M × X → M × Q` exactly when `α` lives over the fundamental class at `b`
for `p`. -/
theorem livesOverFundamentalClass_prodMap_singularHomologyCross_fundamentalClass_iff
    [CompactSpace M] {p : X → Q} {b' : M} {b : Q} (hF : IsClosed (p ⁻¹' {b})) {k m : ℕ}
    (h : d + k = m)
    {α : ((TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)} :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
        (Prod.map id p) (b', b)
        ((TopCat.singularHomologyCross (TopCat.of M) (TopCat.of X) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) d k m h).hom (o.fundamentalClass hd ⊗ₜ α)) ↔
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b α := by
  subst h
  have hloc := o.fiberLocalization_prodMap_singularHomologyCross hd p b' b α
  refine (livesOverFundamentalClass_iff _ _ _ _).trans
    ((not_congr ?_).trans (livesOverFundamentalClass_iff _ _ _ _).symm)
  constructor
  · -- If the localization vanishes, `o b' × α = o b' × ι_* w` for a class `w` of `X ∖ F`, so
    -- `α = ι_* w` comes from `X ∖ F`.
    intro hx
    obtain ⟨w, hw⟩ := o.exists_singularHomologyCrossRel_eq hd p b' b hF (hloc.symm.trans hx)
    have hαw : α = (SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset
        ((p ⁻¹' {b})ᶜ : Set (TopCat.of X))).map) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom w :=
      (o.singularHomologyCrossRelEquiv hd b' X k).injective
        ((singularHomologyCrossRelEquiv_apply _ _ _ _ _ _).trans
          (hw.symm.trans (singularHomologyCrossRelEquiv_apply _ _ _ _ _ _).symm))
    rw [hαw]
    -- `fiberLocalization` is an abbreviation for the map `π` to the relative homology, so its value
    -- at `ι_* w` is `(ι_* ≫ π) w` by `ModuleCat.comp_apply`.
    exact (ConcreteCategory.congr_hom ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ :
      Set (TopCat.of X))).homologyMap_comp_singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) k)
        w).trans (LinearMap.zero_apply _)
  · -- If `α` comes from `X ∖ F`, so does `o b' × α`.
    intro hα
    obtain ⟨w, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of X))).singularHomology_exact_space
        (ModuleCat.of ℤ (ULift.{0} ℤ)) k) α hα
    exact hloc.trans
      (o.singularHomologyMap_singularHomologyCrossRel_homologyMap_eq_zero p b' b w)

end HomologicalOrientation

end TauCeti

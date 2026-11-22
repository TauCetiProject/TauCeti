/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
import TauCeti.CategoryTheory.Preadditive.NSMul

/-!
# Top homology of a closed oriented manifold with flat coefficients

Let `M` be a compact connected manifold of dimension `n` with a homological orientation, and let
`k` be a commutative ring that is flat over `ℤ`, for instance a field of characteristic zero.
The integral fundamental class generates `Hₙ(M; ℤ) ≅ ℤ`, and flat base change
`k ⊗[ℤ] Hₙ(M; ℤ) ≅ Hₙ(M; k)` (`TauCeti.singularHomologyTensorIso`) carries this to the
coefficients `k`. Hence:

* if `k` is moreover nontrivial, the top homology `Hₙ(M; k)` has rank one
  (`TauCeti.HomologicalOrientation.finrank_singularChains_homology_eq_one`);
* a self-map `f` of `M` acts on `Hₙ(M; k)` by multiplication by its degree
  (`TauCeti.HomologicalOrientation.singularHomologyMap_eq_degree_smul_id`), the base change of
  the integral statement `TauCeti.HomologicalOrientation.singularHomologyMap_eq_degree_smul`.

For `k = ℚ` the first statement is also a consequence of
`TauCeti.HomologicalOrientation.rationalFundamentalClassEquiv`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.2, 3.3 and 3.A.
-/

public section

noncomputable section

open CategoryTheory Module
open scoped TensorProduct

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hE : finrank ℝ E = n)

include o hE in
/-- **The top homology of a closed oriented manifold has rank one.** Over a commutative ring `k`
with the strong rank condition that is flat over `ℤ`, such as a field of characteristic zero,
`Hₙ(M; k)` has rank one. -/
theorem finrank_singularChains_homology_eq_one (k : Type) [CommRing k] [StrongRankCondition k]
    [Module.Flat ℤ k] :
    finrank k (((singularChains k).obj (TopCat.of M)).homology n) = 1 := by
  let e : ℤ ≃ₗ[ℤ] ((singularChains ℤ).obj (TopCat.of M)).homology n :=
    (o.fundamentalClassEquiv hE).trans (uliftIntHomologyIso (TopCat.of M) n).toLinearEquiv
  have : Module.Free ℤ (((singularChains ℤ).obj (TopCat.of M)).homology n) := .of_equiv e
  rw [← (singularHomologyTensorIso ℤ k (TopCat.of M) n).toLinearEquiv.finrank_eq,
    Module.finrank_baseChange, ← e.finrank_eq, finrank_self]

/-- **A self-map acts on top homology by its degree, with flat coefficients.** For a self-map `f`
of a compact connected oriented `n`-manifold and a commutative ring `k` flat over `ℤ`, the action
of `f` on `Hₙ(M; k)` is multiplication by the degree of `f`. -/
theorem singularHomologyMap_eq_degree_smul_id (k : Type) [CommRing k] [Module.Flat ℤ k]
    (f : C(M, M)) :
    ContinuousMap.singularHomologyMap k n f = (o.degree o hE f : k) • LinearMap.id := by
  -- First the coefficients `ℤ`, from the coefficients `ULift ℤ` of the fundamental class.
  have hℤ : (HomologicalComplex.homologyMap ((singularChains ℤ).map (TopCat.ofHom f)) n).hom =
      o.degree o hE f • LinearMap.id := by
    have h := homologyMap_comp_uliftIntHomologyIso_hom (TopCat.ofHom f) n
    have hd : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n = o.degree o hE f • 𝟙 _ := by
      ext γ
      have hγ := o.singularHomologyMap_eq_degree_smul hE f γ
      rw [singularHomologyFunctor_obj_map] at hγ
      -- `hγ` types its classes by the singular homology functor, whose value on `M` is the
      -- simplicial homology of `TopCat.toSSet.obj M` by definition
      -- (`singularHomologyFunctor_obj_obj_eq_toSSet_homology`).
      exact hγ
    rw [hd] at h
    exact congrArg ModuleCat.Hom.hom (Iso.eq_zsmul_id_of_zsmul_id_comp_hom _ _ h)
  -- Then flat base change along `ℤ → k`, which sends `d • id` to `d • id`.
  have h := singularHomologyTensorIso_hom_naturality ℤ k (TopCat.ofHom f) n
  have hb : (o.degree o hE f • LinearMap.id :
      ((singularChains ℤ).obj (TopCat.of M)).homology n →ₗ[ℤ] _).baseChange k =
      o.degree o hE f • LinearMap.id := by
    -- The scalar action here is the `zsmul` of the additive group of linear maps, not the module
    -- action `LinearMap.baseChange_smul` is stated for, so go through the additive map
    -- `LinearMap.baseChangeHom`.
    rw [← LinearMap.baseChangeHom_apply, map_zsmul, LinearMap.baseChangeHom_apply,
      LinearMap.baseChange_id]
  have hd : ModuleCat.ofHom (o.degree o hE f • LinearMap.id) =
      o.degree o hE f •
        𝟙 (ModuleCat.of k (k ⊗[ℤ] ((singularChains ℤ).obj (TopCat.of M)).homology n)) :=
    ModuleCat.hom_ext (by simp)
  rw [hℤ, hb, hd] at h
  have h' := Iso.eq_zsmul_id_of_zsmul_id_comp_hom _ _ h
  rw [← Int.cast_smul_eq_zsmul k] at h'
  exact congrArg ModuleCat.Hom.hom h'

end TauCeti.HomologicalOrientation

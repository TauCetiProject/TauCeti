/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.IntegralModel
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
public import TauCeti.Topology.Algebra.RestrictedProduct.Principal
import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Adelic points of affine group schemes as restricted products

Let `F` be a number field, `H` a commutative Hopf `F`-algebra representing an affine group scheme
`G = Spec H`, and `M : IntegralModel F H S` an integral model of `G` away from a finite set `S` of
height-one primes of `𝓞 F`.

Grothendieck's functor-of-points viewpoint defines `G(𝔸_{F,f})` intrinsically as
`WithConv (H →ₐ[F] 𝔸_{F,f})` with the coordinate-evaluation topology (`PointTopology`), whereas
Weil's classical construction defines it as the restricted product of the local groups `G(F_v)`
relative to the integral subgroups `𝓗(𝒪_v)` of a chosen model. Reconciling the two descriptions
(Conrad, Theorem 3.6) shows simultaneously that the restricted product is independent of the choice
of integral model `M` and that the intrinsic adelic group decomposes into local factors carrying
compact open subgroups at almost all places — the foundation for locally compact Hausdorff
structure, Haar and Tamagawa measures, and Hecke-algebra actions on `G(𝔸_F)`.

This file establishes the topological group isomorphism between the finite adelic points
`FiniteAdelicPoints (𝓞 F) F H = G(𝔸_{F,f})` (equipped with the point topology) and the restricted
product `Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]` of local points `G(F_v)` with respect to the
open reference subgroups `M.level v` (compact for `v ∉ S`):

* **Restricted-product homomorphism**: coordinate projections
  `finiteLocalProjection (𝓞 F) F H v : G(𝔸_{F,f}) →* G(F_v)` land in `M.level v` at all but finitely
  many places (`eventually_finiteLocalProjection_mem_level`) and assemble into a continuous group
  homomorphism `M.toRestrictedProductMonoidHom`, with openness at `1` supplied by the open embedding
  `M.finiteAdelicIntegralHom` of model points over the `T`-integral finite adeles (`S ⊆ T`).
* **Restricted-product isomorphism and `T`-integral pieces**: `M.restrictedProductEquiv` upgrades
  `M.toRestrictedProductMonoidHom` to a topological group isomorphism
  `FiniteAdelicPoints (𝓞 F) F H ≃ₜ* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]` whose inverse
  evaluates each coordinate `h ∈ H` place-by-place in `𝔸_{F,f}`, yielding the packaged comparison
  theorem `M.exists_restrictedProductEquiv` and restricting for every finite `T ⊇ S` to a
  topological group isomorphism `M.sIntegralRestrictedProductEquiv T hST` between model points over
  `FiniteAdeleRing.sIntegralAdeles (𝓞 F) F T` and `TauCeti.levelOpenSubgroup M.level T _`.
* **Full adelic decomposition**: combining `AdelicPoints.prodContinuousMulEquiv` with
  `M.restrictedProductEquiv` identifies `G(𝔸_F)` as a topological group with
  `G(F_∞) × Πʳ v, [G(F_v), M.level v]` (`M.adelicRestrictedProductEquiv`).
* **Independence of the integral model**: for any two integral models `M₁` (away from `S₁`) and `M₂`
  (away from `S₂`) of `(F, H)`, their level families `M₁.level` and `M₂.level` agree at all but
  finitely many places (`eventually_level_eq`), inducing a canonical coordinatewise-identity
  topological group isomorphism `M₁.levelChangeEquiv M₂` compatible with `restrictedProductEquiv`
  and satisfying reflexivity, symmetry, and transitivity coherence laws.

## Main declarations

* `TauCeti.IntegralModel.finiteAdelicIntegralHom`: canonical open topological group embedding of
  model points over the `T`-integral finite adeles (`S ⊆ T`) into `FiniteAdelicPoints (𝓞 F) F H`.
* `TauCeti.IntegralModel.toRestrictedProductMonoidHom`,
  `TauCeti.IntegralModel.continuous_toRestrictedProductMonoidHom`: the continuous coordinatewise
  group homomorphism `FiniteAdelicPoints (𝓞 F) F H →* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]`.
* `TauCeti.IntegralModel.restrictedProductEquiv`,
  `TauCeti.IntegralModel.sIntegralRestrictedProductEquiv`: topological group isomorphism
  `FiniteAdelicPoints (𝓞 F) F H ≃ₜ* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]` and its restriction
  for `S ⊆ T` from model points over the `T`-integral adeles to
  `TauCeti.levelOpenSubgroup M.level T _`.
* `TauCeti.IntegralModel.exists_restrictedProductEquiv`: packaged existence and coordinate formula
  for the restricted-product comparison.
* `TauCeti.IntegralModel.adelicRestrictedProductEquiv`: full adelic decomposition
  `AdelicPoints (𝓞 F) F H ≃ₜ* InfinitePoints F H × Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]`.
* `TauCeti.IntegralModel.eventually_level_eq`, `TauCeti.IntegralModel.levelChangeEquiv`,
  `TauCeti.IntegralModel.restrictedProductEquiv_trans_levelChangeEquiv`: independence of the choice
  of integral model.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Rem. 3.5 and Thm. 3.6, pp. 5–6.
* J. S. Milne, *Introduction to Shimura varieties*, §4, pp. 42–43.
-/

public section

open CategoryTheory Filter IsDedekindDomain NumberField TensorProduct Topology WithConv
open scoped RestrictedProduct
open TauCeti.AdelicPoints TauCeti.PointTopology

namespace TauCeti.IntegralModel

universe u

variable {F : Type u} [Field F] [NumberField F] {H : Type u} [CommRing H] [HopfAlgebra F H]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

/-! ### Forward homomorphism into the restricted product and its continuity -/

/-- For any finite adelic point `x ∈ G(𝔸_{F,f})`, its local projection at `v` lies in `M.level v`
for all but finitely many height-one primes `v`. -/
theorem eventually_finiteLocalProjection_mem_level (M : IntegralModel F H S)
    (x : FiniteAdelicPoints (𝓞 F) F H) :
    ∀ᶠ v in cofinite, finiteLocalProjection (𝓞 F) F H v x ∈ M.level v := by
  obtain ⟨s, hs⟩ := M.exists_finset_forall_mem_localPoints_iff
  have hgen : ∀ᶠ v in cofinite,
      ∀ a ∈ s, (x.ofConv (M.toBase a)) v ∈ v.adicCompletionIntegers F :=
    (eventually_all_finset s).mpr fun a _ ↦
      (x.ofConv (M.toBase a)).cofinite_mem_adicCompletionIntegers
  filter_upwards [S.finite_toSet.compl_mem_cofinite, hgen] with v hv hi
  rw [M.level_of_notMem hv, hs v hv]
  intro a ha
  exact (finiteLocalProjection_apply_apply v x (M.toBase a)).symm ▸ hi a ha

/-- The coordinatewise group homomorphism
`G(𝔸_{F,f}) →* Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def toRestrictedProductMonoidHom (M : IntegralModel F H S) :
    FiniteAdelicPoints (𝓞 F) F H →* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v] where
  toFun x := RestrictedProduct.mk (fun v ↦ finiteLocalProjection (𝓞 F) F H v x)
    (M.eventually_finiteLocalProjection_mem_level x)
  map_one' := DFunLike.coe_injective <| funext fun v ↦
    map_one (finiteLocalProjection (𝓞 F) F H v)
  map_mul' x y := DFunLike.coe_injective <| funext fun v ↦
    map_mul (finiteLocalProjection (𝓞 F) F H v) x y

@[simp]
theorem toRestrictedProductMonoidHom_apply (M : IntegralModel F H S)
    (x : FiniteAdelicPoints (𝓞 F) F H) (v : HeightOneSpectrum (𝓞 F)) :
    M.toRestrictedProductMonoidHom x v = finiteLocalProjection (𝓞 F) F H v x := by
  simp [toRestrictedProductMonoidHom, RestrictedProduct.mk_apply]

/-- For `S ⊆ T`, the canonical embedding of model points over the `T`-integral finite adeles
`FiniteAdeleRing.sIntegralAdeles (𝓞 F) F T` into `FiniteAdelicPoints (𝓞 F) F H` under the
generic-fibre identification. -/
noncomputable def finiteAdelicIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    WithConv (M.coordinate →ₐ[SIntegers F S]
        FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) →*
      FiniteAdelicPoints (𝓞 F) F H :=
  letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  M.integralPointsHom
    (FiniteAdeleRing.sIntegralAdelesValOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST))

/-- Unfolding `M.finiteAdelicIntegralHom T hST` as `M.integralPointsHom` along
`FiniteAdeleRing.sIntegralAdelesValOfSubset`. -/
theorem finiteAdelicIntegralHom_def (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    M.finiteAdelicIntegralHom T hST =
      M.integralPointsHom
        (FiniteAdeleRing.sIntegralAdelesValOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)) := by
  rw [finiteAdelicIntegralHom]

@[simp]
theorem finiteAdelicIntegralHom_ofConv_toBase (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    ∀ (x : WithConv (M.coordinate →ₐ[SIntegers F S]
        FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _))) (a : M.coordinate),
      (M.finiteAdelicIntegralHom T hST x).ofConv (M.toBase a) =
        (x.ofConv a : FiniteAdeleRing (𝓞 F) F) := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  intro x a
  rw [M.finiteAdelicIntegralHom_def, M.integralPointsHom_ofConv_toBase,
    FiniteAdeleRing.sIntegralAdelesValOfSubset_apply]

/-- For `S ⊆ T`, `M.finiteAdelicIntegralHom T hST` is injective. -/
theorem finiteAdelicIntegralHom_injective (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Function.Injective (M.finiteAdelicIntegralHom T hST) :=
  letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  M.integralPointsHom_injective
    (FiniteAdeleRing.sIntegralAdelesValOfSubset_injective (𝓞 F) F (Finset.coe_subset.mpr hST))

/-- For `S ⊆ T`, `M.finiteAdelicIntegralHom T hST` is an open topological embedding into
`G(𝔸_{F,f})`. -/
theorem isOpenEmbedding_finiteAdelicIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Topology.IsOpenEmbedding (M.finiteAdelicIntegralHom T hST) := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  rw [M.finiteAdelicIntegralHom_def]
  refine M.isOpenEmbedding_integralPointsHom ?_
  rw [FiniteAdeleRing.coe_sIntegralAdelesValOfSubset]
  exact (FiniteAdeleRing.isOpen_sIntegralAdeles (𝓞 F) F (T : Set _)).isOpenEmbedding_subtypeVal

/-- For `S ⊆ T`, the range of `M.finiteAdelicIntegralHom T hST` consists of the finite adelic points
whose local projections outside `T` lie in `M.level v`. -/
theorem mem_range_finiteAdelicIntegralHom_iff (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {x : FiniteAdelicPoints (𝓞 F) F H} :
    x ∈ (M.finiteAdelicIntegralHom T hST).range ↔
      ∀ v ∉ T, finiteLocalProjection (𝓞 F) F H v x ∈ M.level v := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  rw [M.finiteAdelicIntegralHom_def,
    M.mem_range_integralPointsHom_iff
      (FiniteAdeleRing.sIntegralAdelesValOfSubset_injective (𝓞 F) F (Finset.coe_subset.mpr hST)),
    FiniteAdeleRing.coe_sIntegralAdelesValOfSubset, Subtype.range_coe]
  simp only [SetLike.mem_coe, FiniteAdeleRing.mem_sIntegralAdeles]
  refine ⟨fun hx v hv ↦ ?_, fun hx a v hv ↦ ?_⟩
  · rw [M.level_of_notMem fun hvS ↦ hv (hST hvS), M.mem_localPoints_iff]
    intro a
    exact (finiteLocalProjection_apply_apply v x (M.toBase a)).symm ▸ hx a v hv
  · have hloc := hx v hv
    rw [M.level_of_notMem fun hvS ↦ hv (hST hvS), M.mem_localPoints_iff] at hloc
    exact finiteLocalProjection_apply_apply v x (M.toBase a) ▸ hloc a

/-- The set of finite adelic points whose local projections lie in `M.level v` at every finite
place `v` is open in `G(𝔸_{F,f})`. -/
theorem isOpen_setOf_forall_finiteLocalProjection_mem_level (M : IntegralModel F H S) :
    IsOpen {x : FiniteAdelicPoints (𝓞 F) F H |
      ∀ v, finiteLocalProjection (𝓞 F) F H v x ∈ M.level v} := by
  have heq : {x : FiniteAdelicPoints (𝓞 F) F H |
      ∀ v, finiteLocalProjection (𝓞 F) F H v x ∈ M.level v} =
      (M.finiteAdelicIntegralHom S (Finset.Subset.refl S)).range := by
    ext x
    rw [SetLike.mem_coe, M.mem_range_finiteAdelicIntegralHom_iff S (Finset.Subset.refl S),
      Set.mem_ofPred_eq]
    refine ⟨fun hx v _ ↦ hx v, fun hx v ↦ ?_⟩
    by_cases hv : v ∈ S
    · rw [M.level_of_mem hv]
      exact Subgroup.mem_top _
    · exact hx v hv
  rw [heq]
  exact (M.isOpenEmbedding_finiteAdelicIntegralHom S (Finset.Subset.refl S)).isOpen_range

/-- The coordinatewise homomorphism `M.toRestrictedProductMonoidHom` from finite adelic points to
the restricted product of local points is continuous. -/
@[continuity, fun_prop]
theorem continuous_toRestrictedProductMonoidHom (M : IntegralModel F H S) :
    Continuous M.toRestrictedProductMonoidHom := by
  refine continuous_of_continuousAt_one M.toRestrictedProductMonoidHom ?_
  let U : Set (FiniteAdelicPoints (𝓞 F) F H) :=
    {x | ∀ v, finiteLocalProjection (𝓞 F) F H v x ∈ M.level v}
  have h1U : (1 : FiniteAdelicPoints (𝓞 F) F H) ∈ U := fun v ↦ by
    rw [map_one]
    exact one_mem _
  have hU_cont : Continuous (fun u : U ↦ M.toRestrictedProductMonoidHom u.val) := by
    rw [TauCeti.continuous_restrictedProduct_iff_of_forall_mem (T := Set.univ)
      (le_principal_iff.mpr univ_mem) (fun u v _ ↦ by
        rw [M.toRestrictedProductMonoidHom_apply]
        exact u.property v)]
    exact continuous_pi fun v ↦ (continuous_finiteLocalProjection v).comp continuous_subtypeVal
  exact (continuousOn_iff_continuous_domRestrict.mpr hU_cont).continuousAt
    (M.isOpen_setOf_forall_finiteLocalProjection_mem_level.mem_nhds h1U)

/-! ### Inverse map from the restricted product and its continuity -/

private theorem eventually_eval_baseChange_mem_integers (M : IntegralModel F H S)
    (t : F ⊗[SIntegers F S] M.coordinate) :
    ∀ᶠ v in cofinite, ∀ g ∈ M.level v,
      g.ofConv (M.baseChangeIso.hom.hom t) ∈ v.adicCompletionIntegers F := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    filter_upwards [S.finite_toSet.compl_mem_cofinite,
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).cofinite_mem_adicCompletionIntegers]
      with v hv hc g hg
    have hc_int : algebraMap F (v.adicCompletion F) c ∈ v.adicCompletionIntegers F := by
      rwa [FiniteAdeleRing.algebraMap_apply_eq_algebraMap] at hc
    rw [M.level_of_notMem hv, M.mem_localPoints_iff] at hg
    rw [M.baseChangeIso_hom_tmul, map_smul, Algebra.smul_def]
    exact mul_mem hc_int (hg a)
  | add t₁ t₂ ih₁ ih₂ =>
    filter_upwards [ih₁, ih₂] with v hv₁ hv₂ g hg
    rw [map_add, map_add]
    exact add_mem (hv₁ g hg) (hv₂ g hg)

/-- For every coordinate `h ∈ H`, elements of `M.level v` take `v`-integral values at `h` for all
but finitely many height-one primes `v`. -/
theorem eventually_eval_mem_adicCompletionIntegers_of_mem_level (M : IntegralModel F H S)
    (h : H) :
    ∀ᶠ v in cofinite, ∀ g ∈ M.level v, g.ofConv h ∈ v.adicCompletionIntegers F := by
  filter_upwards [eventually_eval_baseChange_mem_integers M (M.baseChangeIso.inv.hom h)]
    with v hv g hg
  simpa only [M.baseChangeIso.inv_hom_id_apply] using hv g hg

private noncomputable def adeleEval (M : IntegralModel F H S) (h : H) :
    (Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlong
    (fun v : HeightOneSpectrum (𝓞 F) ↦ LocalPoints (𝓞 F) F H v)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A₁ := fun v ↦ (M.level v : Set (LocalPoints (𝓞 F) F H v)))
    (A₂ := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    id tendsto_id (fun _ g ↦ g.ofConv h)
    (M.eventually_eval_mem_adicCompletionIntegers_of_mem_level h)

private theorem adeleEval_apply (M : IntegralModel F H S) (h : H)
    (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    adeleEval M h y v = (y v).ofConv h :=
  RestrictedProduct.mapAlong_apply _ _ _ _ _ _ y v

private theorem continuous_adeleEval (M : IntegralModel F H S) (h : H) :
    Continuous (adeleEval M h) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum (𝓞 F) ↦ LocalPoints (𝓞 F) F H v)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A₁ := fun v ↦ (M.level v : Set (LocalPoints (𝓞 F) F H v)))
    (A₂ := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    id tendsto_id (fun _ g ↦ g.ofConv h)
    (M.eventually_eval_mem_adicCompletionIntegers_of_mem_level h)
    (fun _ ↦ continuous_eval_ofConv h)

private noncomputable def fromRestrictedProductFun (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) : FiniteAdelicPoints (𝓞 F) F H :=
  toConv
    { toFun h := adeleEval M h y
      map_one' := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_one, FiniteAdeleRing.one_apply]
      map_mul' h₁ h₂ := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_mul, FiniteAdeleRing.mul_apply,
          adeleEval_apply, adeleEval_apply]
      map_zero' := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_zero, FiniteAdeleRing.zero_apply]
      map_add' h₁ h₂ := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_add, FiniteAdeleRing.add_apply,
          adeleEval_apply, adeleEval_apply]
      commutes' c := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, AlgHom.commutes, FiniteAdeleRing.algebraMap_apply_eq_algebraMap] }

private theorem fromRestrictedProductFun_ofConv_apply (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) (h : H) (v : HeightOneSpectrum (𝓞 F)) :
    ((fromRestrictedProductFun M y).ofConv h) v = (y v).ofConv h :=
  adeleEval_apply M h y v

private theorem continuous_fromRestrictedProductFun (M : IntegralModel F H S) :
    Continuous (fromRestrictedProductFun M) :=
  continuous_withConv_iff.mpr fun h ↦ continuous_adeleEval M h

/-! ### Packaged restricted-product equivalence -/

/-- **Adelic points as a restricted product**: for an integral model `M` of `G = Spec H` away from
`S`, coordinate projections induce a topological group isomorphism between `G(𝔸_{F,f})` and the
restricted product `Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def restrictedProductEquiv (M : IntegralModel F H S) :
    FiniteAdelicPoints (𝓞 F) F H ≃ₜ* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v] where
  toMulEquiv :=
    { toFun := M.toRestrictedProductMonoidHom
      invFun := fromRestrictedProductFun M
      left_inv x := ofConv_injective <| AlgHom.ext fun h ↦ FiniteAdeleRing.ext F fun v ↦ by
        rw [fromRestrictedProductFun_ofConv_apply, M.toRestrictedProductMonoidHom_apply]
        exact finiteLocalProjection_apply_apply v x h
      right_inv y := DFunLike.coe_injective <| funext fun v ↦
        ofConv_injective <| AlgHom.ext fun h ↦ by
          rw [M.toRestrictedProductMonoidHom_apply]
          exact (finiteLocalProjection_apply_apply v (fromRestrictedProductFun M y) h).trans
            (fromRestrictedProductFun_ofConv_apply M y h v)
      map_mul' := map_mul M.toRestrictedProductMonoidHom }
  continuous_toFun := M.continuous_toRestrictedProductMonoidHom
  continuous_invFun := continuous_fromRestrictedProductFun M

@[simp]
theorem restrictedProductEquiv_apply (M : IntegralModel F H S)
    (x : FiniteAdelicPoints (𝓞 F) F H) (v : HeightOneSpectrum (𝓞 F)) :
    M.restrictedProductEquiv x v = finiteLocalProjection (𝓞 F) F H v x := by
  simp [restrictedProductEquiv]

@[simp]
theorem toMonoidHom_restrictedProductEquiv (M : IntegralModel F H S) :
    (M.restrictedProductEquiv :
      FiniteAdelicPoints (𝓞 F) F H →* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) =
      M.toRestrictedProductMonoidHom := by
  ext x : 1
  ext v
  simp

/-- Coordinate evaluation of `M.restrictedProductEquiv`. -/
theorem restrictedProductEquiv_apply_ofConv_apply (M : IntegralModel F H S)
    (x : FiniteAdelicPoints (𝓞 F) F H) (v : HeightOneSpectrum (𝓞 F)) (h : H) :
    (M.restrictedProductEquiv x v).ofConv h = (x.ofConv h) v := by
  rw [M.restrictedProductEquiv_apply]
  exact finiteLocalProjection_apply_apply v x h

@[simp]
theorem restrictedProductEquiv_symm_ofConv_apply (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) (h : H) (v : HeightOneSpectrum (𝓞 F)) :
    ((M.restrictedProductEquiv.symm y).ofConv h) v = (y v).ofConv h := by
  rw [← M.restrictedProductEquiv_apply_ofConv_apply, ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem finiteLocalProjection_restrictedProductEquiv_symm (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    finiteLocalProjection (𝓞 F) F H v (M.restrictedProductEquiv.symm y) = y v := by
  rw [← M.restrictedProductEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

theorem restrictedProductEquiv_finiteDiagonal (M : IntegralModel F H S)
    (g : WithConv (H →ₐ[F] F)) (v : HeightOneSpectrum (𝓞 F)) :
    M.restrictedProductEquiv (finiteDiagonal (𝓞 F) F H g) v =
      AlgHom.mapValue (Algebra.ofId F (v.adicCompletion F)) g := by
  rw [M.restrictedProductEquiv_apply, finiteLocalProjection_finiteDiagonal]

/-- Characterization of `T`-integral rational points in terms of `M.restrictedProductEquiv`. -/
theorem mem_globalPoints_iff_restrictedProductEquiv (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ v ∉ T, M.restrictedProductEquiv (finiteDiagonal (𝓞 F) F H g) v ∈ M.level v := by
  simp only [M.restrictedProductEquiv_finiteDiagonal, M.mem_globalPoints_iff_forall_level hST,
    localProjection_diagonal]

/-- **Restricted-product comparison theorem** (Conrad, Theorem 3.6): for any integral model `M` of
`G = Spec H` away from `S`, there is a topological group isomorphism
`FiniteAdelicPoints (𝓞 F) F H ≃ₜ* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]` acting coordinatewise
on evaluations. -/
theorem exists_restrictedProductEquiv (M : IntegralModel F H S) :
    ∃ e : FiniteAdelicPoints (𝓞 F) F H ≃ₜ* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v],
      ∀ (x : FiniteAdelicPoints (𝓞 F) F H) (v : HeightOneSpectrum (𝓞 F)) (h : H),
        (e x v).ofConv h = (x.ofConv h) v :=
  ⟨M.restrictedProductEquiv, M.restrictedProductEquiv_apply_ofConv_apply⟩

/-- For a finite set of places `T ⊇ S`, restricting `M.restrictedProductEquiv` along
`M.finiteAdelicIntegralHom T hST` identifies model points over the `T`-integral finite adeles
`FiniteAdeleRing.sIntegralAdeles (𝓞 F) F T` as a topological group with the open subgroup
`TauCeti.levelOpenSubgroup M.level T _` of the restricted product cut out by `M.level` outside
`T`. -/
noncomputable def sIntegralRestrictedProductEquiv (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    WithConv (M.coordinate →ₐ[SIntegers F S]
        FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) ≃ₜ*
      TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v) :=
  letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  let φ := ((M.restrictedProductEquiv :
      FiniteAdelicPoints (𝓞 F) F H →* Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]).comp
    (M.finiteAdelicIntegralHom T hST)).codRestrict
    (TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v)) fun x ↦ by
      rw [TauCeti.mem_levelOpenSubgroup]
      intro v hv
      rw [MonoidHom.comp_apply, MonoidHom.coe_ofClass, M.restrictedProductEquiv_apply]
      exact (M.mem_range_finiteAdelicIntegralHom_iff T hST).mp
        (MonoidHom.mem_range.mpr ⟨x, rfl⟩) v hv
  have hφ : Topology.IsEmbedding φ :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp <|
      M.restrictedProductEquiv.toHomeomorph.isEmbedding.comp
        (M.isOpenEmbedding_finiteAdelicIntegralHom T hST).isEmbedding
  have hsurj : Function.Surjective φ := by
    intro y
    have hy := (TauCeti.mem_levelOpenSubgroup M.level T _ y.val).mp y.property
    obtain ⟨x, hx⟩ := (M.mem_range_finiteAdelicIntegralHom_iff T hST
      (x := M.restrictedProductEquiv.symm y.val)).mpr fun v hv ↦ by simpa using hy v hv
    exact ⟨x, Subtype.ext <| by
      rw [MonoidHom.codRestrict_apply, Subtype.coe_mk, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
        hx, ContinuousMulEquiv.apply_symm_apply]⟩
  ContinuousMulEquiv.mk' (hφ.toHomeomorphOfSurjective hsurj) (map_mul φ)

/-- Coercing `M.sIntegralRestrictedProductEquiv T hST x` into the ambient restricted product agrees
with applying `M.restrictedProductEquiv` to `M.finiteAdelicIntegralHom T hST x`. -/
@[simp]
theorem val_sIntegralRestrictedProductEquiv_apply (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    ∀ x : WithConv (M.coordinate →ₐ[SIntegers F S]
        FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)),
      ((M.sIntegralRestrictedProductEquiv T hST x :
          TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v)) :
        Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) =
        M.restrictedProductEquiv (M.finiteAdelicIntegralHom T hST x) := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  intro x
  exact (congrArg Subtype.val <|
    (congrFun (ContinuousMulEquiv.coe_mk' _ _) x).trans
      (Topology.IsEmbedding.toHomeomorphOfSurjective_apply _ _ x)).trans <| by
    rw [MonoidHom.codRestrict_apply, Subtype.coe_mk, MonoidHom.comp_apply, MonoidHom.coe_ofClass]

/-- Coordinate evaluation of `M.sIntegralRestrictedProductEquiv T hST` on `M.toBase`; not marked
`@[simp]` because `simp` already reduces the left-hand side via
`val_sIntegralRestrictedProductEquiv_apply` and `finiteAdelicIntegralHom_ofConv_toBase`. -/
theorem sIntegralRestrictedProductEquiv_apply_ofConv_toBase (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    ∀ (x : WithConv (M.coordinate →ₐ[SIntegers F S]
        FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)))
      (v : HeightOneSpectrum (𝓞 F)) (a : M.coordinate),
      (((M.sIntegralRestrictedProductEquiv T hST x :
          TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v)) :
        Πʳ w, [LocalPoints (𝓞 F) F H w, M.level w]) v).ofConv (M.toBase a) =
        (x.ofConv a : FiniteAdeleRing (𝓞 F) F) v := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  intro x v a
  simp

/-- Embedding `(M.sIntegralRestrictedProductEquiv T hST).symm y` into `G(𝔸_{F,f})` agrees with
applying `M.restrictedProductEquiv.symm` to `(y : Πʳ v, [G(F_v), M.level v])`. -/
@[simp]
theorem finiteAdelicIntegralHom_sIntegralRestrictedProductEquiv_symm (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T)
    (y : TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v)) :
    M.finiteAdelicIntegralHom T hST ((M.sIntegralRestrictedProductEquiv T hST).symm y) =
      M.restrictedProductEquiv.symm (y : Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  apply M.restrictedProductEquiv.injective
  rw [← M.val_sIntegralRestrictedProductEquiv_apply T hST,
    ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]

/-- Placewise coordinate evaluation of `(M.sIntegralRestrictedProductEquiv T hST).symm`. -/
@[simp]
theorem sIntegralRestrictedProductEquiv_symm_ofConv_apply (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
      FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
    ∀ (y : TauCeti.levelOpenSubgroup M.level T (fun v _ ↦ M.isOpen_level v))
      (a : M.coordinate) (v : HeightOneSpectrum (𝓞 F)),
      (((M.sIntegralRestrictedProductEquiv T hST).symm y).ofConv a :
          FiniteAdeleRing (𝓞 F) F) v =
        ((y : Πʳ w, [LocalPoints (𝓞 F) F H w, M.level w]) v).ofConv (M.toBase a) := by
  let : Algebra (SIntegers F S) (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (T : Set _)) :=
    FiniteAdeleRing.sIntegralAdelesAlgebraOfSubset (𝓞 F) F (Finset.coe_subset.mpr hST)
  intro y a v
  rw [← M.finiteAdelicIntegralHom_ofConv_toBase T hST,
    M.finiteAdelicIntegralHom_sIntegralRestrictedProductEquiv_symm,
    M.restrictedProductEquiv_symm_ofConv_apply]

/-- Full adelic restricted-product decomposition: `G(𝔸_F)` is canonically isomorphic as a
topological group to `G(F_∞) × Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def adelicRestrictedProductEquiv (M : IntegralModel F H S) :
    AdelicPoints (𝓞 F) F H ≃ₜ*
      InfinitePoints F H × Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v] :=
  (AdelicPoints.prodContinuousMulEquiv (𝓞 F) F H).trans
    ((ContinuousMulEquiv.refl (InfinitePoints F H)).prodCongr M.restrictedProductEquiv)

@[simp]
theorem adelicRestrictedProductEquiv_fst (M : IntegralModel F H S) (x : AdelicPoints (𝓞 F) F H) :
    (M.adelicRestrictedProductEquiv x).1 = infiniteProjection (𝓞 F) F H x := by
  simp [adelicRestrictedProductEquiv]

@[simp]
theorem adelicRestrictedProductEquiv_snd (M : IntegralModel F H S) (x : AdelicPoints (𝓞 F) F H) :
    (M.adelicRestrictedProductEquiv x).2 =
      M.restrictedProductEquiv (finiteProjection (𝓞 F) F H x) := by
  simp [adelicRestrictedProductEquiv]

/-- Coordinate formula for the second factor of `M.adelicRestrictedProductEquiv`; not marked
`@[simp]` because `simp` already reduces it to `finiteLocalProjection` applied to
`finiteProjection`. -/
theorem adelicRestrictedProductEquiv_snd_apply (M : IntegralModel F H S)
    (x : AdelicPoints (𝓞 F) F H) (v : HeightOneSpectrum (𝓞 F)) :
    (M.adelicRestrictedProductEquiv x).2 v = localProjection (𝓞 F) F H v x := by
  rw [M.adelicRestrictedProductEquiv_snd, M.restrictedProductEquiv_apply, ← localProjection_apply]

@[simp]
theorem adelicRestrictedProductEquiv_symm_apply (M : IntegralModel F H S)
    (p : InfinitePoints F H × Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) :
    M.adelicRestrictedProductEquiv.symm p =
      (AdelicPoints.prodContinuousMulEquiv (𝓞 F) F H).symm
        (p.1, M.restrictedProductEquiv.symm p.2) := by
  rw [adelicRestrictedProductEquiv, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.prodCongr_symm, ContinuousMulEquiv.prodCongr_apply,
    (ContinuousMulEquiv.refl _).symm_apply_eq.mpr (ContinuousMulEquiv.refl_apply _ p.1).symm]

/-! ### Independence of the integral model -/

section ModelIndependence

private theorem eventually_localPoints_le
    {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    ∀ᶠ v in cofinite, ∀ (hv₁ : v ∉ S₁) (hv₂ : v ∉ S₂),
      M₂.localPoints v hv₂ ≤ M₁.localPoints v hv₁ := by
  obtain ⟨s₁, hs₁⟩ := M₁.exists_finset_forall_mem_localPoints_iff
  have hgen : ∀ᶠ v in cofinite, ∀ a ∈ s₁, ∀ g ∈ M₂.level v,
      g.ofConv (M₁.toBase a) ∈ v.adicCompletionIntegers F :=
    (eventually_all_finset s₁).mpr fun a _ ↦
      M₂.eventually_eval_mem_adicCompletionIntegers_of_mem_level (M₁.toBase a)
  filter_upwards [hgen] with v hv hv₁ hv₂ g hg
  rw [hs₁ v hv₁]
  intro a ha
  exact hv a ha g ((M₂.level_of_notMem hv₂).symm ▸ hg)

/-- **Model independence of local integral subgroups**: for any two integral models `M₁` and `M₂` of
the same affine group scheme `(F, H)`, their reference subgroups `M₁.level v` and `M₂.level v` agree
at all but finitely many height-one primes `v`. -/
theorem eventually_level_eq {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    ∀ᶠ v in cofinite, M₁.level v = M₂.level v := by
  filter_upwards [S₁.finite_toSet.compl_mem_cofinite, S₂.finite_toSet.compl_mem_cofinite,
    eventually_localPoints_le M₁ M₂, eventually_localPoints_le M₂ M₁] with v hv₁ hv₂ h₂₁ h₁₂
  rw [M₁.level_of_notMem hv₁, M₂.level_of_notMem hv₂]
  exact le_antisymm (h₁₂ hv₂ hv₁) (h₂₁ hv₁ hv₂)

/-- The canonical coordinatewise-identity topological group isomorphism between the restricted
products attached to two integral models `M₁` and `M₂` of `(F, H)`. -/
noncomputable def levelChangeEquiv {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    (Πʳ v, [LocalPoints (𝓞 F) F H v, M₁.level v]) ≃ₜ*
      Πʳ v, [LocalPoints (𝓞 F) F H v, M₂.level v] where
  toMulEquiv := TauCeti.restrictedProductCongr M₁.level M₂.level (M₁.eventually_level_eq M₂)
  continuous_toFun :=
    TauCeti.continuous_restrictedProductCongr M₁.level M₂.level (M₁.eventually_level_eq M₂)
  continuous_invFun :=
    TauCeti.continuous_restrictedProductCongr_symm M₁.level M₂.level (M₁.eventually_level_eq M₂)

@[simp]
theorem toMulEquiv_levelChangeEquiv {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    (M₁.levelChangeEquiv M₂ :
      (Πʳ v, [LocalPoints (𝓞 F) F H v, M₁.level v]) ≃*
        Πʳ v, [LocalPoints (𝓞 F) F H v, M₂.level v]) =
      TauCeti.restrictedProductCongr M₁.level M₂.level (M₁.eventually_level_eq M₂) :=
  (rfl)

@[simp]
theorem levelChangeEquiv_apply {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂)
    (x : Πʳ v, [LocalPoints (𝓞 F) F H v, M₁.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    M₁.levelChangeEquiv M₂ x v = x v :=
  (congrArg (fun y ↦ y v) (DFunLike.congr_fun (M₁.toMulEquiv_levelChangeEquiv M₂) x)).trans
    (TauCeti.restrictedProductCongr_apply M₁.level M₂.level _ x v)

@[simp]
theorem levelChangeEquiv_refl (M : IntegralModel F H S) :
    M.levelChangeEquiv M =
      ContinuousMulEquiv.refl (Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]) := by
  ext x : 1
  ext v
  simp

@[simp]
theorem levelChangeEquiv_symm {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    (M₁.levelChangeEquiv M₂).symm = M₂.levelChangeEquiv M₁ := by
  ext x : 1
  rw [ContinuousMulEquiv.symm_apply_eq]
  ext v
  simp

/-- Coordinate formula for `(M₁.levelChangeEquiv M₂).symm`; not marked `@[simp]` because `simp`
already simplifies it via `levelChangeEquiv_symm` and `levelChangeEquiv_apply`. -/
theorem levelChangeEquiv_symm_apply {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂)
    (x : Πʳ v, [LocalPoints (𝓞 F) F H v, M₂.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    (M₁.levelChangeEquiv M₂).symm x v = x v := by
  simp

@[simp]
theorem levelChangeEquiv_trans {S₁ S₂ S₃ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂)
    (M₃ : IntegralModel F H S₃) :
    (M₁.levelChangeEquiv M₂).trans (M₂.levelChangeEquiv M₃) =
      M₁.levelChangeEquiv M₃ := by
  ext x : 1
  ext v
  simp

/-- Composing `M₁.restrictedProductEquiv` with the canonical level-change isomorphism
`M₁.levelChangeEquiv M₂` recovers `M₂.restrictedProductEquiv`. -/
@[simp]
theorem restrictedProductEquiv_trans_levelChangeEquiv {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    M₁.restrictedProductEquiv.trans (M₁.levelChangeEquiv M₂) = M₂.restrictedProductEquiv := by
  ext x : 1
  ext v
  simp

end ModelIndependence

end TauCeti.IntegralModel

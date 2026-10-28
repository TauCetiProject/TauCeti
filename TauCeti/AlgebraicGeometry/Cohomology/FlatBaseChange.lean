/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.FiveLemma
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Flat
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine

/-!
# The flat base change map on cohomology is an isomorphism

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a ring map and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` with projection `g : Y ⟶ X`. For
a sheaf of modules `M` on `X`, the pullback map on cohomology
`Scheme.Hom.cohomologyPullback g M n : Hⁿ(X, M) →+ Hⁿ(Y, g^* M)` is `R`-linear, so it extends to
an `R'`-linear map

`TauCeti.AlgebraicGeometry.cohomologyBaseChange H M n : R' ⊗_R Hⁿ(X, M) →ₗ[R'] Hⁿ(Y, g^* M)`.

This file proves that this canonical map is an isomorphism in every degree when `R → R'` is flat,
`M` is quasi-coherent and `X` is quasi-compact with affine diagonal (for instance quasi-compact
and separated): this is flat base change over an affine base (Stacks 02KH, Hartshorne III.9.3).
Unlike `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top`,
which computes both sides by Čech complexes of a chosen cover, the isomorphism here does not depend
on any choice, and it is compatible with the maps induced by morphisms of sheaves and with the
connecting maps of short exact sequences. Over a field `k` and a field extension `K / k` it shows
that the dimension of `Hⁿ(X, M)` does not change when `k` is extended to `K`.

The proof is by dimension shifting, simultaneously for all quasi-coherent sheaves. In degree zero
the map is the flat base change of global sections
(`TauCeti.AlgebraicGeometry.linearEquivTensorCohomologyZeroPullback`). Choose a finite affine open
cover `U` of `X`. Every quasi-coherent `M` embeds into the quasi-coherent sheaf
`I = ⨁ᵢ (U i).ι_* (M|_{U i})`, which has no higher cohomology on `X` because each open immersion
`(U i).ι` is affine. By the Čech computation, `g^* I` has no higher cohomology on `Y` either. The
pullback of `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` is exact because `g` is flat, and the five lemma, applied to the
two long exact sequences, shows that the map in degree `n + 1` for `M` is bijective as soon as
those in degree `n` for `I` and `Q` are.

## Main declarations

* `TauCeti.AlgebraicGeometry.cohomologyBaseChange`: the canonical map
  `R' ⊗_R Hⁿ(X, M) →ₗ[R'] Hⁿ(Y, g^* M)`, characterized by `cohomologyBaseChange_tmul`;
* `TauCeti.AlgebraicGeometry.bijective_cohomologyBaseChange`: it is bijective for flat
  `R → R'`, quasi-coherent `M` and `X` quasi-compact with affine diagonal;
* `TauCeti.AlgebraicGeometry.cohomologyMapBaseLinear_comp_cohomologyBaseChange` and
  `TauCeti.AlgebraicGeometry.cohomologyδBaseLinear_comp_cohomologyBaseChange`: its naturality and
  its compatibility with connecting maps;
* `TauCeti.AlgebraicGeometry.cohomologyBaseChangeLinearEquiv`: the resulting flat base change
  isomorphism;
* `TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_pullback_of_isPullback`: invariance of
  the dimension and finite-dimensionality of `Hⁿ(X, M)` under extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open TauCeti.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section Embedding

variable {X : Scheme.{u}}

/-- Every quasi-coherent sheaf `M` on a quasi-compact scheme with affine diagonal embeds into a
quasi-coherent sheaf with no cohomology in positive degrees, namely the direct sum of the
pushforwards of the restrictions of `M` to the members of a finite affine open cover. -/
private lemma exists_mono_isQuasicoherent_subsingleton_cohomology [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (I : X.Modules) (i : M ⟶ I), I.IsQuasicoherent ∧ Mono i ∧
      ∀ k, Subsingleton (Cohomology I (k + 1)) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  have hU (i : 𝒰.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (𝒰.f i)
  have hcover : ⨆ i, U i = ⊤ := 𝒰.iSup_opensRange
  -- An affine open of a scheme with affine diagonal is an affine morphism.
  have hι (i : 𝒰.I₀) : IsAffineHom (U i).ι := ⟨fun V hV ↦
    (U i).ι.isAffineOpen_iff_of_isOpenImmersion.mp (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact (hU i).inf hV)⟩
  have : HasFiniteBiproducts X.Modules := .of_hasFiniteProducts
  let F : 𝒰.I₀ → X.Modules := fun i ↦
    (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)
  have hF (i : 𝒰.I₀) : (F i).IsQuasicoherent := by
    have := isQuasicoherent_restrictFunctor (U i).ι M
    exact isQuasicoherent_pushforward_of_isAffineHom (U i).ι _
  refine ⟨⨁ F, biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app M,
    isQuasicoherent_of_isColimit (K := Discrete.functor F) (fun j ↦ hF j.as)
      (biproduct.isColimit F), ⟨fun {T} a b hab ↦ ?_⟩, fun k ↦ ?_⟩
  · -- A section of `M` is determined by its restrictions to the members of the cover.
    ext W t
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      (fun i ↦ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W)) W (fun i ↦ homOfLE ((U i).ι.image_preimage_le W))
      ?_ _ _ fun i ↦ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, U i := hcover.symm ▸ trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
      refine Opens.mem_iSup.mpr ⟨i, ?_⟩
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hi, hx⟩
    · have := congrArg (fun φ ↦ (φ ≫ biproduct.π F i).app W t) hab
      simp only [Category.assoc, biproduct.lift_π, Scheme.Modules.Hom.comp_app,
        restrictAdjunction_unit_app_app] at this
      exact this
  · -- Each summand has no higher cohomology, being pushed forward from an affine scheme along an
    -- affine morphism; so neither has their direct sum.
    have hzero (i : 𝒰.I₀) : IsZero ((cohomologyFunctor X (k + 1)).obj (F i)) := by
      have : IsAffine (U i).toScheme := hU i
      have := isQuasicoherent_restrictFunctor (U i).ι M
      have : Subsingleton (Cohomology (F i) (k + 1)) :=
        ((U i).ι.cohomologyPushforwardIsoOfIsAffineHom U hU hcover _
          (k + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
            (subsingleton_cohomology_succ_of_isAffine _ k)
      exact @AddCommGrpCat.isZero_of_subsingleton _ this
    refine AddCommGrpCat.subsingleton_of_isZero (G := (cohomologyFunctor X (k + 1)).obj (⨁ F)) ?_
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← biproduct.total,
      Functor.map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [CategoryTheory.Functor.map_comp, (hzero i).eq_of_tgt ((cohomologyFunctor X (k + 1)).map
      (biproduct.π F i)) 0, zero_comp]

end Embedding

section FlatBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

include H in
/-- The base change `g` carries the action of the base ring `R` to the action of `R'`, through
`algebraMap R R'`, on global functions. -/
private lemma appTop_baseRingToGlobalSections (r : R) :
    g.appTop (baseRingToGlobalSections R X r) =
      baseRingToGlobalSections R' Y (algebraMap R R' r) := by
  have h := congrArg (fun φ ↦ φ.hom r)
    (baseRingToStructurePresheaf_app_comp_appLE_of_isPullback H (W := ⊤) (W' := ⊤) le_top)
  simp only [Scheme.baseRingToStructurePresheaf_app_top, CommRingCat.comp_apply,
    CommRingCat.hom_ofHom] at h
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact h

include H in
/-- The pullback map on cohomology along the base change `g` is `R`-linear, for the action of `R`
on the target through `algebraMap R R'`. -/
private lemma cohomologyPullback_base_smul (M : X.Modules) (n : ℕ) (r : R)
    (x : Cohomology M n) :
    g.cohomologyPullback M n (r • x) = algebraMap R R' r • g.cohomologyPullback M n x := by
  rw [base_smul_cohomology, base_smul_cohomology, g.cohomologyPullback_smul,
    appTop_baseRingToGlobalSections H]

/-- The flat base change map `R' ⊗_R Hⁿ(X, M) →ₗ[R'] Hⁿ(Y, g^* M)` for the base change
`Y = X ×_R R'` along a ring map `R → R'`: the `R'`-linear extension of the pullback map on
cohomology. It is an isomorphism when `R → R'` is flat, `M` is quasi-coherent and `X` is
quasi-compact with affine diagonal (`bijective_cohomologyBaseChange`). -/
def cohomologyBaseChange (M : X.Modules) (n : ℕ) :
    R' ⊗[R] Cohomology M n →ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n :=
  letI : Module R (Cohomology ((Scheme.Modules.pullback g).obj M) n) :=
    Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (Cohomology ((Scheme.Modules.pullback g).obj M) n) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  LinearMap.liftBaseChange R'
    { toFun := g.cohomologyPullback M n
      map_add' := map_add _
      map_smul' := cohomologyPullback_base_smul H M n }

/-- The flat base change map sends `r' ⊗ x` to `r'` times the pullback of `x`. -/
@[simp]
lemma cohomologyBaseChange_tmul (M : X.Modules) (n : ℕ) (r' : R') (x : Cohomology M n) :
    cohomologyBaseChange H M n (r' ⊗ₜ x) = r' • g.cohomologyPullback M n x :=
  (rfl)

/-- The flat base change map is natural in the coefficient sheaf. -/
theorem cohomologyMapBaseLinear_comp_cohomologyBaseChange {M N : X.Modules} (α : M ⟶ N) (n : ℕ) :
    (cohomologyMapBaseLinear R' Y ((Scheme.Modules.pullback g).map α) n).comp
        (cohomologyBaseChange H M n) =
      (cohomologyBaseChange H N n).comp ((cohomologyMapBaseLinear R X α n).baseChange R') := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul r' x =>
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      cohomologyBaseChange_tmul, cohomologyBaseChange_tmul, LinearMap.map_smul]
    congr 1
    rw [cohomologyMapBaseLinear_apply, cohomologyMapBaseLinear_apply, cohomologyFunctor_map,
      cohomologyFunctor_map]
    exact (g.cohomologyPullback_cohomologyMap α n x).symm

/-- The flat base change map commutes with the connecting maps of a short exact sequence whose
pullback is short exact. -/
theorem cohomologyδBaseLinear_comp_cohomologyBaseChange {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hS' : (S.map (Scheme.Modules.pullback g)).ShortExact) (n : ℕ) :
    (cohomologyδBaseLinear R' Y hS' n (n + 1) rfl).comp (cohomologyBaseChange H S.X₃ n) =
      (cohomologyBaseChange H S.X₁ (n + 1)).comp
        ((cohomologyδBaseLinear R X hS n (n + 1) rfl).baseChange R') := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul r' x =>
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      cohomologyBaseChange_tmul, cohomologyBaseChange_tmul, LinearMap.map_smul]
    congr 1
    rw [cohomologyδBaseLinear_apply, cohomologyδBaseLinear_apply]
    exact (g.cohomologyPullback_cohomologyδ hS hS' rfl x).symm

include H in
/-- In degree zero the flat base change map is the flat base change of global sections. -/
private lemma bijective_cohomologyBaseChange_zero [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    Function.Bijective (cohomologyBaseChange H M 0) := by
  have : cohomologyBaseChange H M 0 =
      (linearEquivTensorCohomologyZeroPullback H M).toLinearMap := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul r' x =>
      rw [show r' ⊗ₜ[R] x = r' • ((1 : R') ⊗ₜ[R] x) by rw [smul_tmul', smul_eq_mul, mul_one],
        LinearMap.map_smul, LinearMap.map_smul, cohomologyBaseChange_tmul, one_smul,
        LinearEquiv.coe_coe]
      refine congrArg (r' • ·) ?_
      exact (cohomologyZeroEquiv _).injective ((g.cohomologyZeroEquiv_cohomologyPullback M x).trans
        (linearEquivTensorCohomologyZeroPullback_one_tmul H M x).symm)
  rw [this]
  exact (linearEquivTensorCohomologyZeroPullback H M).bijective

include H in
/-- **Flat base change for the cohomology of quasi-coherent sheaves.** Let `X` be a quasi-compact
scheme with affine diagonal over `R`, for instance a quasi-compact separated one, let `R → R'` be
a flat ring map and let `Y = X ×_R R'`, given as a pullback square with projection `g`. Then for
every quasi-coherent sheaf `M` on `X` and every `n`, the canonical map
`R' ⊗_R Hⁿ(X, M) ⟶ Hⁿ(Y, g^* M)`, `r' ⊗ x ↦ r' • g^* x`, is bijective. -/
theorem bijective_cohomologyBaseChange [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : Function.Bijective (cohomologyBaseChange H M n) := by
  have : QuasiSeparatedSpace X :=
    have : QuasiSeparated (terminal.from X) := ⟨inferInstance⟩
    quasiSeparatedSpace_of_quasiSeparated (terminal.from X)
  have : Flat g := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    exact MorphismProperty.of_isPullback H.flip inferInstance
  induction n generalizing M with
  | zero => exact bijective_cohomologyBaseChange_zero H M
  | succ n ih =>
    obtain ⟨I, i, hI, hi, hIX⟩ := exists_mono_isQuasicoherent_subsingleton_cohomology M
    -- The short exact sequence `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` and its pullback along the flat map `g`.
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_of_g_is_cokernel S
      (cokernelIsCokernel i)) hi inferInstance
    have hS' : (S.map (Scheme.Modules.pullback g)).ShortExact :=
      g.shortExact_map_pullback_of_flat S hS
    -- `g^* I` has no higher cohomology on `Y` either, by the Čech computation of base change.
    have hIY : Subsingleton (Cohomology ((Scheme.Modules.pullback g).obj I) (n + 1)) := by
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top H I
        (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) (fun s hs ↦ by
          rw [Finset.inf_eq_iInf]
          exact IsAffineOpen.biInf _ s.finite_toSet hs fun i _ ↦ isAffineOpen_opensRange (𝒰.f i))
        𝒰.iSup_opensRange (n + 1)
      have := hIX n
      exact e.toEquiv.subsingleton_congr.mp inferInstance
    have := hIX n
    -- The base-linear maps of the long exact sequences are the maps on cohomology.
    have eX : ⇑(cohomologyMapBaseLinear R X S.g n) = ⇑(cohomologyMap S.g n) := funext fun x ↦ by
      rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]; rfl
    have eY : ⇑(cohomologyMapBaseLinear R' Y ((Scheme.Modules.pullback g).map S.g) n) =
        ⇑(cohomologyMap ((Scheme.Modules.pullback g).map S.g) n) := funext fun x ↦ by
      rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]; rfl
    have δX : ⇑(cohomologyδBaseLinear R X hS n (n + 1) rfl) = ⇑(cohomologyδ hS n (n + 1) rfl) :=
      funext (cohomologyδBaseLinear_apply R X hS n (n + 1) rfl)
    have δY : ⇑(cohomologyδBaseLinear R' Y hS' n (n + 1) rfl) =
        ⇑(cohomologyδ hS' n (n + 1) rfl) :=
      funext (cohomologyδBaseLinear_apply R' Y hS' n (n + 1) rfl)
    have hexX : Function.Exact (cohomologyMapBaseLinear R X S.g n)
        (cohomologyδBaseLinear R X hS n (n + 1) rfl) := by
      rw [eX, δX]
      exact exact_cohomologyMap_cohomologyδ hS n (n + 1) rfl
    exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
      ((cohomologyMapBaseLinear R X S.g n).baseChange R')
      ((cohomologyδBaseLinear R X hS n (n + 1) rfl).baseChange R')
      (cohomologyMapBaseLinear R' Y ((Scheme.Modules.pullback g).map S.g) n)
      (cohomologyδBaseLinear R' Y hS' n (n + 1) rfl)
      (cohomologyBaseChange H I n) (cohomologyBaseChange H (cokernel i) n)
      (cohomologyBaseChange H M (n + 1))
      (cohomologyMapBaseLinear_comp_cohomologyBaseChange H S.g n)
      (cohomologyδBaseLinear_comp_cohomologyBaseChange H hS hS' n)
      (by
        rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
        exact Module.Flat.lTensor_exact R' hexX)
      (by
        rw [eY, δY]
        exact exact_cohomologyMap_cohomologyδ hS' n (n + 1) rfl)
      (ih I).2 (ih (cokernel i))
      (LinearMap.baseChange_surjective _ (by
        rw [δX]
        exact cohomologyδ_surjective hS n (n + 1) rfl (hIX n)))
      (by
        rw [δY]
        exact cohomologyδ_surjective hS' n (n + 1) rfl hIY)

/-- **Flat base change for the cohomology of quasi-coherent sheaves**, as the canonical linear
equivalence `R' ⊗_R Hⁿ(X, M) ≃ₗ[R'] Hⁿ(Y, g^* M)` for a quasi-coherent sheaf `M` on a quasi-compact
scheme `X` with affine diagonal over `R` and a flat ring map `R → R'`. -/
def cohomologyBaseChangeLinearEquiv [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n :=
  LinearEquiv.ofBijective (cohomologyBaseChange H M n) (bijective_cohomologyBaseChange H M n)

/-- The flat base change isomorphism sends `r' ⊗ x` to `r'` times the pullback of `x`. -/
@[simp]
lemma cohomologyBaseChangeLinearEquiv_tmul [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (r' : R') (x : Cohomology M n) :
    cohomologyBaseChangeLinearEquiv H M n (r' ⊗ₜ x) = r' • g.cohomologyPullback M n x :=
  (rfl)

end FlatBaseChange

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- The dimension of `Hⁿ(X, M)` does not change under extension of the base field, for a
quasi-coherent sheaf `M` on a quasi-compact scheme over a field with affine diagonal, for instance a
separated scheme of finite type. The coefficients after base change are the canonical pullback
sheaf. -/
theorem finrank_cohomology_pullback_eq_of_isPullback [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    Module.finrank K (Cohomology ((Scheme.Modules.pullback g).obj M) n) =
      Module.finrank k (Cohomology M n) := by
  rw [← (cohomologyBaseChangeLinearEquiv H M n).finrank_eq, Module.finrank_baseChange]

include H in
/-- The cohomology `Hⁿ(X, M)` of a quasi-coherent sheaf stays finite-dimensional under extension of
the base field, on a quasi-compact scheme over a field with affine diagonal. -/
theorem finiteDimensional_cohomology_pullback_of_isPullback [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) [FiniteDimensional k (Cohomology M n)] :
    FiniteDimensional K (Cohomology ((Scheme.Modules.pullback g).obj M) n) :=
  Module.Finite.equiv (cohomologyBaseChangeLinearEquiv H M n)

end Field

end TauCeti.AlgebraicGeometry

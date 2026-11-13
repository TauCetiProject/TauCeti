/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
import Mathlib.Algebra.FiveLemma
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Flat
import TauCeti.AlgebraicGeometry.Scheme.Induction

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
The dimension, finite-dimensionality and Euler-characteristic corollaries hold for every
quasi-compact quasi-separated scheme: the open-set equivalence below, applied at the whole
space, supplies the needed linear equivalence.

The proof is by dimension shifting, simultaneously for all quasi-coherent sheaves. In degree zero
the map is the flat base change of global sections
(`TauCeti.AlgebraicGeometry.linearEquivTensorCohomologyZeroPullback`). Choose a finite affine open
cover `U` of `X`. Every quasi-coherent `M` embeds into the quasi-coherent sheaf
`I = ⨁ᵢ (U i).ι_* (M|_{U i})`, which has no higher cohomology on `X` because each open immersion
`(U i).ι` is affine. By the Čech computation, `g^* I` has no higher cohomology on `Y` either. The
pullback of `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` is exact because `g` is flat, and the five lemma, applied to the
two long exact sequences, shows that the map in degree `n + 1` for `M` is bijective as soon as
those in degree `n` for `I` and `Q` are.

The same construction on the cohomology of an open subset `U` of `X`, from the pullback
`Scheme.Hom.cohomologyOnPullback`, is the base change map

`cohomologyOnBaseChange H M n U : R' ⊗_R Hⁿ(U, M) →ₗ[R'] Hⁿ(g⁻¹ U, g^* M)`.

It is bijective for flat `R → R'` and quasi-coherent `M` on every quasi-compact quasi-separated
open `U`, with no separation hypothesis on `X`. The proof is a Mayer-Vietoris induction on the
number of affine opens covering `U`
(`AlgebraicGeometry.Scheme.Opens.induction_on_isCompact_isQuasiSeparated`). On an affine open the
map is the flat base change of sections in degree zero, and both sides vanish in positive degrees
because `g` is affine. Pullback commutes with restriction and with the Mayer-Vietoris connecting
maps (`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_mayerVietorisδ`), and tensoring with the
flat `R'` keeps the Mayer-Vietoris sequence of `U ∪ V` exact, so the five lemma gives the map of
`U ∪ V` in degree `n + 1` from those of `U`, `V` and `U ∩ V`
(`TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange_sup_succ`). In degree zero the map is
the flat base change of sections over a quasi-compact quasi-separated open
(`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections_of_isQuasiSeparated`).

## Main declarations

* `TauCeti.AlgebraicGeometry.cohomologyBaseChange`: the canonical map
  `R' ⊗_R Hⁿ(X, M) →ₗ[R'] Hⁿ(Y, g^* M)`, characterized by `cohomologyBaseChange_tmul`;
* `TauCeti.AlgebraicGeometry.bijective_cohomologyBaseChange`: it is bijective for flat
  `R → R'`, quasi-coherent `M` and `X` quasi-compact with affine diagonal;
* `TauCeti.AlgebraicGeometry.bijective_cohomologyBaseChange_zero`: in degree zero it is bijective
  for every quasi-compact quasi-separated `X`, being the flat base change of global sections
  (`TauCeti.AlgebraicGeometry.linearEquivTensorCohomologyZeroPullback_toLinearMap`);
* `TauCeti.AlgebraicGeometry.cohomologyMapBaseLinear_comp_cohomologyBaseChange` and
  `TauCeti.AlgebraicGeometry.cohomologyδBaseLinear_comp_cohomologyBaseChange`: its naturality and
  its compatibility with connecting maps;
* `TauCeti.AlgebraicGeometry.cohomologyBaseChangeLinearEquiv`: the resulting flat base change
  isomorphism, whose underlying linear map is `cohomologyBaseChange`
  (`TauCeti.AlgebraicGeometry.cohomologyBaseChangeLinearEquiv_toLinearMap`);
* `TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_pullback_of_isPullback`: invariance of
  the dimension and finite-dimensionality of `Hⁿ(X, M)` under extension of the base field,
  `TauCeti.AlgebraicGeometry.finrank_cohomology_trivial_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_trivial_of_isPullback`: their
  specialisation to the structure sheaf, whose pullback is identified with `𝒪_Y`, with
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_trivial_of_isPullback_of_isProper` the
  finite-dimensionality for a proper scheme, and
  `TauCeti.AlgebraicGeometry.eulerCharBelow_pullback_eq_of_isPullback`: the same invariance of the
  truncated Euler characteristic `Scheme.Modules.eulerCharBelow`;
* `TauCeti.AlgebraicGeometry.cohomologyOnBaseChange`: the base change map on the cohomology of an
  open subset, characterized by `cohomologyOnBaseChange_tmul`;
* `TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange_zero` and
  `TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange_sup_succ`: its bijectivity in degree
  zero on a quasi-compact quasi-separated open, and its propagation along the Mayer-Vietoris
  sequence;
* `TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange` and
  `TauCeti.AlgebraicGeometry.cohomologyOnBaseChangeLinearEquiv`: flat base change
  `R' ⊗_R Hⁿ(U, M) ≅ Hⁿ(g⁻¹ U, g^* M)` on every quasi-compact quasi-separated open `U`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), and Lemmas
  30.4.2–30.4.6 (tag 01XH) for the Mayer-Vietoris induction.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open TauCeti.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section FlatBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

section Aux

variable (M : X.Modules) (U V : X.Opens) [Algebra R Γ(X, ⊤)] [Algebra R' Γ(Y, ⊤)]
  [∀ W : X.Opens, Module R Γ(M, W)] [∀ W : X.Opens, IsScalarTower R Γ(X, ⊤) Γ(M, W)]
  [∀ W' : Y.Opens, Module R' Γ((Scheme.Modules.pullback g).obj M, W')]
  [∀ W' : Y.Opens, IsScalarTower R' Γ(Y, ⊤) Γ((Scheme.Modules.pullback g).obj M, W')]
  [∀ W' : Y.Opens, Module R Γ((Scheme.Modules.pullback g).obj M, W')]
  [∀ W' : Y.Opens, IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, W')]

/-- Pulling back sections commutes with the restriction of `H⁰` to the two members of a cover. -/
lemma mayerVietorisSectionsRestrictionLinear_comm_cohomologyPullback
    [IsScalarTower R Γ(X, ⊤) (Cohomology M 0)]
    [IsScalarTower R' Γ(Y, ⊤) (Cohomology ((Scheme.Modules.pullback g).obj M) 0)]
    [Module R (Cohomology ((Scheme.Modules.pullback g).obj M) 0)]
    [IsScalarTower R R' (Cohomology ((Scheme.Modules.pullback g).obj M) 0)]
    (σU : Γ(M, U) →ₗ[R] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U))
    (σV : Γ(M, V) →ₗ[R] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ V))
    (h₁ : Cohomology M 0 →ₗ[R] Cohomology ((Scheme.Modules.pullback g).obj M) 0)
    (hσU : ∀ s, σU s = g.pullbackSections M U s) (hσV : ∀ s, σV s = g.pullbackSections M V s)
    (h₁_apply : ∀ x, h₁ x = g.cohomologyPullback M 0 x) :
    (σU.prodMap σV).comp (((mayerVietorisSectionsRestrictionLinear M U V).comp
        (cohomologyZeroLinearEquiv M).toLinearMap).restrictScalars R) =
      ((((mayerVietorisSectionsRestrictionLinear ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (g ⁻¹ᵁ V)).comp (cohomologyZeroLinearEquiv _).toLinearMap).restrictScalars
          R').restrictScalars R).comp h₁ := by
  refine LinearMap.ext fun x ↦ ?_
  -- Pullback lands in sections over `g ⁻¹ᵁ ⊤`, which is `⊤` by definition.
  have hx := mayerVietorisSectionsRestrictionLinear_apply ((Scheme.Modules.pullback g).obj M)
    (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) (g.pullbackSections M ⊤ (cohomologyZeroEquiv M x))
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.prodMap_apply, cohomologyZeroLinearEquiv_apply,
    mayerVietorisSectionsRestrictionLinear_apply, h₁_apply,
    g.cohomologyZeroEquiv_cohomologyPullback, hσU, hσV]
  refine Eq.trans ?_ hx.symm
  -- Pullback of sections commutes with the restrictions from `⊤` to `U` and to `V`.
  exact Prod.ext (g.pullbackSections_restrict M ⊤ U.leTop _).symm
    (g.pullbackSections_restrict M ⊤ V.leTop _).symm

end Aux

include H in
/-- The pullback map on cohomology along the base change `g` is `R`-linear, for the action of `R`
on the target through `algebraMap R R'`. -/
private lemma cohomologyPullback_base_smul (M : X.Modules) (n : ℕ) (r : R)
    (x : Cohomology M n) :
    g.cohomologyPullback M n (r • x) = algebraMap R R' r • g.cohomologyPullback M n x := by
  rw [base_smul_cohomology, base_smul_cohomology, g.cohomologyPullback_smul,
    appTop_baseRingToGlobalSections_of_isPullback H]

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

/-- In degree zero the flat base change map is the flat base change isomorphism of global
sections `linearEquivTensorCohomologyZeroPullback`, for `R → R'` flat, `M` quasi-coherent and `X`
quasi-compact and quasi-separated. -/
lemma linearEquivTensorCohomologyZeroPullback_toLinearMap [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    (linearEquivTensorCohomologyZeroPullback H M).toLinearMap = cohomologyBaseChange H M 0 := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul r' x =>
    rw [show r' ⊗ₜ[R] x = r' • ((1 : R') ⊗ₜ[R] x) by rw [smul_tmul', smul_eq_mul, mul_one],
      LinearMap.map_smul, LinearMap.map_smul, cohomologyBaseChange_tmul, one_smul,
      LinearEquiv.coe_coe]
    refine congrArg (r' • ·) ?_
    exact (cohomologyZeroEquiv _).injective
      ((linearEquivTensorCohomologyZeroPullback_one_tmul H M x).trans
        (g.cohomologyZeroEquiv_cohomologyPullback M x).symm)

/-- **Flat base change in degree zero.** For a flat ring map `R → R'` and a quasi-coherent sheaf
`M` on a quasi-compact quasi-separated scheme `X` over `R`, the canonical map
`R' ⊗_R H⁰(X, M) ⟶ H⁰(Y, g^* M)` is bijective. -/
theorem bijective_cohomologyBaseChange_zero [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    Function.Bijective (cohomologyBaseChange H M 0) := by
  rw [← linearEquivTensorCohomologyZeroPullback_toLinearMap]
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
    obtain ⟨I, i, hI, hi, hIX⟩ := M.exists_mono_isQuasicoherent_subsingleton_cohomology
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
        (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange)
        (fun s hs ↦ IsAffineOpen.finset_inf s hs fun i _ ↦ isAffineOpen_opensRange (𝒰.f i))
        𝒰.iSup_opensRange (n + 1)
      have := hIX n
      exact e.toEquiv.subsingleton_congr.mp inferInstance
    have := hIX n
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
        exact Module.Flat.lTensor_exact R'
          (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R X hS n))
      (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R' Y hS' n)
      (ih I).2 (ih (cokernel i))
      (LinearMap.baseChange_surjective _ (by
        rw [coe_cohomologyδBaseLinear]
        exact cohomologyδ_surjective hS n (n + 1) rfl (hIX n)))
      (by
        rw [coe_cohomologyδBaseLinear]
        exact cohomologyδ_surjective hS' n (n + 1) rfl hIY)

/-- **Flat base change for the cohomology of quasi-coherent sheaves**, as the canonical linear
equivalence `R' ⊗_R Hⁿ(X, M) ≃ₗ[R'] Hⁿ(Y, g^* M)` for a quasi-coherent sheaf `M` on a quasi-compact
scheme `X` with affine diagonal over `R` and a flat ring map `R → R'`. -/
def cohomologyBaseChangeLinearEquiv [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n :=
  LinearEquiv.ofBijective (cohomologyBaseChange H M n) (bijective_cohomologyBaseChange H M n)

/-- The underlying linear map of the flat base change isomorphism is the canonical base change
map `cohomologyBaseChange`. -/
@[simp]
lemma cohomologyBaseChangeLinearEquiv_toLinearMap [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    (cohomologyBaseChangeLinearEquiv H M n).toLinearMap = cohomologyBaseChange H M n :=
  (rfl)

/-- The flat base change isomorphism sends `r' ⊗ x` to `r'` times the pullback of `x`. -/
@[simp]
lemma cohomologyBaseChangeLinearEquiv_tmul [Module.Flat R R'] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (r' : R') (x : Cohomology M n) :
    cohomologyBaseChangeLinearEquiv H M n (r' ⊗ₜ x) = r' • g.cohomologyPullback M n x :=
  (rfl)

section Opens

variable (M : X.Modules)

include H in
/-- Pullback on the cohomology of an open is `R`-linear, for the action of `R` on the target
through `algebraMap R R'`. -/
private lemma cohomologyOnPullback_base_smul (n : ℕ) (U : X.Opens) (r : R)
    (x : cohomologyOn M n U) :
    g.cohomologyOnPullback M n U (r • x) = algebraMap R R' r • g.cohomologyOnPullback M n U x := by
  rw [base_smul_cohomologyOn, base_smul_cohomologyOn, g.cohomologyOnPullback_smul,
    appTop_baseRingToGlobalSections_of_isPullback H]

/-- The flat base change map `R' ⊗_R Hⁿ(U, M) →ₗ[R'] Hⁿ(g⁻¹ U, g^* M)` on an open subset `U` of
`X`, for the base change `Y = X ×_R R'`: the `R'`-linear extension of pullback on the cohomology of
`U`. It is an isomorphism when `R → R'` is flat, `M` is quasi-coherent and `U` is quasi-compact and
quasi-separated (`bijective_cohomologyOnBaseChange`). -/
def cohomologyOnBaseChange (n : ℕ) (U : X.Opens) :
    R' ⊗[R] cohomologyOn M n U →ₗ[R']
      cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U) :=
  letI : Module R (cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U)) :=
    Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U)) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  LinearMap.liftBaseChange R'
    { toFun := g.cohomologyOnPullback M n U
      map_add' := map_add _
      map_smul' := cohomologyOnPullback_base_smul H M n U }

/-- The flat base change map on an open sends `r' ⊗ x` to `r'` times the pullback of `x`. -/
@[simp]
lemma cohomologyOnBaseChange_tmul (n : ℕ) (U : X.Opens) (r' : R') (x : cohomologyOn M n U) :
    cohomologyOnBaseChange H M n U (r' ⊗ₜ x) = r' • g.cohomologyOnPullback M n U x :=
  (rfl)

/-- The base change maps on the cohomology of opens commute with restriction. -/
lemma cohomologyOnRes_cohomologyOnBaseChange_tmul (n : ℕ) {U V : X.Opens} (h : U ≤ V) (r' : R')
    (x : cohomologyOn M n V) :
    cohomologyOnRes ((Scheme.Modules.pullback g).obj M) n (g.preimage_mono h)
        (cohomologyOnBaseChange H M n V (r' ⊗ₜ x)) =
      cohomologyOnBaseChange H M n U (r' ⊗ₜ cohomologyOnRes M n h x) := by
  rw [cohomologyOnBaseChange_tmul, cohomologyOnBaseChange_tmul, base_smul_cohomologyOn,
    base_smul_cohomologyOn, ← cohomologyOnResLinear_apply, LinearMap.map_smul,
    cohomologyOnResLinear_apply]
  exact congrArg _
    (ConcreteCategory.congr_hom (g.cohomologyOnRes_comp_cohomologyOnPullback M n h) x).symm

/-- The base change maps on the cohomology of opens commute with the Mayer-Vietoris connecting
maps of `U ∪ V` and of `g⁻¹ U ∪ g⁻¹ V`. -/
lemma mayerVietorisδ_cohomologyOnBaseChange_tmul (U V : X.Opens) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (r' : R') (x : cohomologyOn M n₀ (U ⊓ V)) :
    mayerVietorisδ ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n₀ n₁ h
        (cohomologyOnBaseChange H M n₀ (U ⊓ V) (r' ⊗ₜ x)) =
      cohomologyOnBaseChange H M n₁ (U ⊔ V) (r' ⊗ₜ mayerVietorisδ M U V n₀ n₁ h x) := by
  let N := (Scheme.Modules.pullback g).obj M
  -- `R'` acts on the cohomology of `Y` through global functions, which commute with `δ`.
  have hδ (y : cohomologyOn N n₀ (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) :
      mayerVietorisδ N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n₀ n₁ h (r' • y) =
        r' • mayerVietorisδ N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n₀ n₁ h y := by
    rw [base_smul_cohomologyOn, base_smul_cohomologyOn, ← mayerVietorisδLinear_apply,
      LinearMap.map_smul, mayerVietorisδLinear_apply]
  exact (hδ _).trans
    (congrArg (r' • ·) (g.cohomologyOnPullback_mayerVietorisδ M U V n₀ n₁ h x).symm)

/-- **Flat base change in degree zero on an open.** For a flat ring map `R → R'`, a
quasi-coherent sheaf `M` on `X` and a quasi-compact quasi-separated open `U`, the base change map
`R' ⊗_R H⁰(U, M) ⟶ H⁰(g⁻¹ U, g^* M)` is bijective: it is the flat base change of sections over
`U`. -/
theorem bijective_cohomologyOnBaseChange_zero [Module.Flat R R'] [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    Function.Bijective (cohomologyOnBaseChange H M 0 U) := by
  let N := (Scheme.Modules.pullback g).obj M
  let : Module R Γ(M, U) := Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op U)).hom
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(M, U) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R' Γ(N, g ⁻¹ᵁ U) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ U))).hom
  let : Algebra R' Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  have : IsScalarTower R' Γ(Y, g ⁻¹ᵁ U) Γ(N, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R Γ(N, g ⁻¹ᵁ U) := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' Γ(N, g ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hσ : IsBaseChange R' (g.pullbackSectionsBaseLinear M U H.toCommSq) :=
    g.isBaseChange_pullbackSections_of_isQuasiSeparated M H hU hU'
  -- Degree-zero cohomology is sections, compatibly with the base-ring actions.
  let eX : cohomologyOn M 0 U ≃ₗ[R] Γ(M, U) :=
    { cohomologyOnZeroEquiv M U with
      map_smul' := fun r x ↦ by
        -- State the action of `R` on sections through `baseRingToStructurePresheaf`, whose
        -- value on `U` is computed by `Scheme.baseRingToStructurePresheaf_app`.
        change cohomologyOnZeroEquiv M U (r • x) =
          ((X.baseRingToStructurePresheaf R).app (op U)).hom r • cohomologyOnZeroEquiv M U x
        rw [base_smul_cohomologyOn, cohomologyOnZeroEquiv_smul,
          Scheme.baseRingToStructurePresheaf_app]
        rfl }
  have heY (r' : R') (y : cohomologyOn N 0 (g ⁻¹ᵁ U)) :
      cohomologyOnZeroEquiv N (g ⁻¹ᵁ U) (r' • y) = r' • cohomologyOnZeroEquiv N (g ⁻¹ᵁ U) y := by
    -- As for `eX`, state the action of `R'` on sections through `baseRingToStructurePresheaf`.
    change _ = ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ U))).hom r' •
      cohomologyOnZeroEquiv N (g ⁻¹ᵁ U) y
    rw [base_smul_cohomologyOn, cohomologyOnZeroEquiv_smul, Scheme.baseRingToStructurePresheaf_app]
    rfl
  have hcomp : ⇑(cohomologyOnZeroEquiv N (g ⁻¹ᵁ U)) ∘ cohomologyOnBaseChange H M 0 U =
      hσ.equiv ∘ LinearMap.lTensor R' eX.toLinearMap := by
    ext z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]
    | tmul r' x =>
      simp only [Function.comp_apply, cohomologyOnBaseChange_tmul, LinearMap.lTensor_tmul,
        IsBaseChange.equiv_tmul, heY]
      exact congrArg (r' • ·) ((g.cohomologyOnZeroEquiv_cohomologyOnPullback M U x).trans
        (g.pullbackSectionsBaseLinear_apply M U H.toCommSq _).symm)
  rw [← (cohomologyOnZeroEquiv N (g ⁻¹ᵁ U)).bijective.of_comp_iff', hcomp]
  exact hσ.equiv.bijective.comp (LinearEquiv.lTensor R' eX).bijective

/-- **Flat base change propagates along the Mayer-Vietoris sequence.** For a flat ring map
`R → R'` and open subsets `U` and `V` of `X`, the base change map of `U ⊔ V` is bijective in
degree `n + 1` as soon as those of `U` and `V` are surjective in degree `n` and bijective in degree
`n + 1`, and that of `U ⊓ V` is bijective in degree `n` and injective in degree `n + 1`. -/
theorem bijective_cohomologyOnBaseChange_sup_succ [Module.Flat R R'] {U V : X.Opens} (n : ℕ)
    (hU₀ : Function.Surjective (cohomologyOnBaseChange H M n U))
    (hV₀ : Function.Surjective (cohomologyOnBaseChange H M n V))
    (hUV₀ : Function.Bijective (cohomologyOnBaseChange H M n (U ⊓ V)))
    (hU₁ : Function.Bijective (cohomologyOnBaseChange H M (n + 1) U))
    (hV₁ : Function.Bijective (cohomologyOnBaseChange H M (n + 1) V))
    (hUV₁ : Function.Injective (cohomologyOnBaseChange H M (n + 1) (U ⊓ V))) :
    Function.Bijective (cohomologyOnBaseChange H M (n + 1) (U ⊔ V)) := by
  -- The five lemma, for the Mayer-Vietoris sequence of `U ∪ V` tensored with `R'` (exact since
  -- `R'` is flat) mapping to that of `g⁻¹ U ∪ g⁻¹ V`. The vertical maps are the base change maps,
  -- with the inverse images of `U ⊓ V` and `U ⊔ V` written as the intersection and union of those
  -- of `U` and `V`, and `hfrom`, `hδ` and `hto` are the commuting squares.
  let N := (Scheme.Modules.pullback g).obj M
  let : Algebra R Γ(X, ⊤) := (baseRingToGlobalSections R X).toAlgebra
  have (k : ℕ) (W : X.Opens) : IsScalarTower R Γ(X, ⊤) (cohomologyOn M k W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let i (k : ℕ) := ((cohomologyOnBaseChange H M k U).prodMap (cohomologyOnBaseChange H M k V)) ∘ₗ
    (TensorProduct.prodRight R R' R' _ _).toLinearMap
  have hi (k : ℕ) (r' : R') (p : cohomologyOn M k U × cohomologyOn M k V) :
      i k (r' ⊗ₜ p) =
        (cohomologyOnBaseChange H M k U (r' ⊗ₜ p.1), cohomologyOnBaseChange H M k V (r' ⊗ₜ p.2)) :=
    rfl
  let iInf (k : ℕ) : R' ⊗[R] cohomologyOn M k (U ⊓ V) →ₗ[R'] cohomologyOn N k (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) :=
    cohomologyOnBaseChange H M k (U ⊓ V)
  let iSup : R' ⊗[R] cohomologyOn M (n + 1) (U ⊔ V) →ₗ[R']
      cohomologyOn N (n + 1) (g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V) :=
    cohomologyOnBaseChange H M (n + 1) (U ⊔ V)
  have hfrom (k : ℕ) :
      (mayerVietorisFromProdLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) k).toAddMonoidHom.comp
          (i k).toAddMonoidHom =
        (iInf k).toAddMonoidHom.comp
          (((mayerVietorisFromProdLinear M U V k).restrictScalars R).lTensor
            R').toAddMonoidHom := by
    refine AddMonoidHom.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul r' p =>
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, hi,
        mayerVietorisFromProdLinear_apply, tmul_sub, map_sub]
      exact congrArg₂ (· - ·)
        (cohomologyOnRes_cohomologyOnBaseChange_tmul H M k (inf_le_left : U ⊓ V ≤ U) r' p.1)
        (cohomologyOnRes_cohomologyOnBaseChange_tmul H M k (inf_le_right : U ⊓ V ≤ V) r' p.2)
  have hδ :
      (mayerVietorisδLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n (n + 1) rfl).toAddMonoidHom.comp
          (iInf n).toAddMonoidHom =
        iSup.toAddMonoidHom.comp
          (((mayerVietorisδLinear M U V n (n + 1) rfl).restrictScalars R).lTensor
            R').toAddMonoidHom := by
    refine AddMonoidHom.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul r' x =>
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, mayerVietorisδLinear_apply]
      exact mayerVietorisδ_cohomologyOnBaseChange_tmul H M U V n (n + 1) rfl r' x
  have hto :
      (mayerVietorisToProdLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) (n + 1)).toAddMonoidHom.comp
          iSup.toAddMonoidHom =
        (i (n + 1)).toAddMonoidHom.comp
          (((mayerVietorisToProdLinear M U V (n + 1)).restrictScalars R).lTensor
            R').toAddMonoidHom := by
    refine AddMonoidHom.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul r' x =>
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
        mayerVietorisToProdLinear_apply, hi]
      exact Prod.ext
        (cohomologyOnRes_cohomologyOnBaseChange_tmul H M (n + 1) (le_sup_left : U ≤ U ⊔ V) r' x)
        (cohomologyOnRes_cohomologyOnBaseChange_tmul H M (n + 1) (le_sup_right : V ≤ U ⊔ V) r' x)
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    _ _ _ _ _ _ _ _ (i n).toAddMonoidHom _ _ (i (n + 1)).toAddMonoidHom _
    (hfrom n) hδ hto (hfrom (n + 1))
    (Module.Flat.lTensor_exact R' (exact_mayerVietorisFromProdLinear_mayerVietorisδLinear M U V n))
    (Module.Flat.lTensor_exact R' (exact_mayerVietorisδLinear_mayerVietorisToProdLinear M U V n))
    (Module.Flat.lTensor_exact R'
      (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear M U V (n + 1)))
    (exact_mayerVietorisFromProdLinear_mayerVietorisδLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n)
    (exact_mayerVietorisδLinear_mayerVietorisToProdLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) n)
    (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear N (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) (n + 1))
    ((hU₀.prodMap hV₀).comp (TensorProduct.prodRight R R' R' _ _).surjective) hUV₀
    ((hU₁.prodMap hV₁).comp (TensorProduct.prodRight R R' R' _ _).bijective) hUV₁

/-- On an affine open `U`, the base change map is bijective in positive degrees: both `U` and its
inverse image, which is affine since `g` is, have no higher quasi-coherent cohomology. -/
private lemma bijective_cohomologyOnBaseChange_succ_of_isAffineOpen [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (cohomologyOnBaseChange H M (n + 1) U) := by
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen M hU n
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen ((Scheme.Modules.pullback g).obj M)
    (hU.preimage g) n
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Flat base change for the cohomology of quasi-coherent sheaves on quasi-compact
quasi-separated opens.** Let `R → R'` be a flat ring map, `Y = X ×_R R'` with projection `g`, and
`M` a quasi-coherent sheaf on `X`. For every quasi-compact and quasi-separated open `U` of `X` and
every `n`, the canonical map `R' ⊗_R Hⁿ(U, M) ⟶ Hⁿ(g⁻¹ U, g^* M)`, `r' ⊗ x ↦ r' • g^* x`, is
bijective. No separation hypothesis on `X` is needed. -/
theorem bijective_cohomologyOnBaseChange [Module.Flat R R'] [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ) :
    Function.Bijective (cohomologyOnBaseChange H M n U) := by
  refine Scheme.Opens.induction_on_isCompact_isQuasiSeparated
    (P := fun U ↦ ∀ n, Function.Bijective (cohomologyOnBaseChange H M n U)) U hU hU' ?_ ?_ n
  · rintro V hV (_ | n)
    · exact bijective_cohomologyOnBaseChange_zero H M hV.isCompact hV.isQuasiSeparated
    · exact bijective_cohomologyOnBaseChange_succ_of_isAffineOpen H M hV n
  · rintro V W hV hW hVW hPV hPW hPVW (_ | n)
    · exact bijective_cohomologyOnBaseChange_zero H M (hV.union hW) hVW
    · exact bijective_cohomologyOnBaseChange_sup_succ H M n (hPV n).2 (hPW n).2 (hPVW n)
        (hPV (n + 1)) (hPW (n + 1)) (hPVW (n + 1)).1

/-- **Flat base change for the cohomology of quasi-coherent sheaves on quasi-compact
quasi-separated opens**, as the canonical linear equivalence
`R' ⊗_R Hⁿ(U, M) ≃ₗ[R'] Hⁿ(g⁻¹ U, g^* M)` for a flat ring map `R → R'`. -/
def cohomologyOnBaseChangeLinearEquiv [Module.Flat R R'] [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ) :
    R' ⊗[R] cohomologyOn M n U ≃ₗ[R']
      cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U) :=
  LinearEquiv.ofBijective (cohomologyOnBaseChange H M n U)
    (bijective_cohomologyOnBaseChange H M hU hU' n)

/-- The flat base change isomorphism on an open is the canonical base change map
`cohomologyOnBaseChange`. -/
@[simp]
lemma cohomologyOnBaseChangeLinearEquiv_apply [Module.Flat R R'] [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ)
    (z : R' ⊗[R] cohomologyOn M n U) :
    cohomologyOnBaseChangeLinearEquiv H M hU hU' n z = cohomologyOnBaseChange H M n U z :=
  (rfl)

end Opens

include H in
/-- Global cohomology of a quasi-coherent sheaf on a quasi-compact quasi-separated scheme
commutes with flat base change, as an existence statement for a linear equivalence. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback_of_quasiSeparated
    [Module.Flat R R'] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R']
      Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  let eX : cohomologyOn M n ⊤ ≃ₗ[R] Cohomology M n :=
    { __ := (cohomologyOnTopLinearEquiv M n).toAddEquiv
      map_smul' r x := by
        rw [base_smul_cohomologyOn, base_smul_cohomology]
        exact (cohomologyOnTopLinearEquiv M n).map_smul _ _ }
  let N := (Scheme.Modules.pullback g).obj M
  let eY : cohomologyOn N n ⊤ ≃ₗ[R'] Cohomology N n :=
    { __ := (cohomologyOnTopLinearEquiv N n).toAddEquiv
      map_smul' r x := by
        rw [base_smul_cohomologyOn, base_smul_cohomology]
        exact (cohomologyOnTopLinearEquiv N n).map_smul _ _ }
  -- The top open coerces to the universal set; the explicit types fix the open argument
  -- of the base-change equivalence while using the global compactness instances.
  let e := cohomologyOnBaseChangeLinearEquiv H M
    (show IsCompact ((⊤ : X.Opens) : Set X) from isCompact_univ)
    (show IsQuasiSeparated ((⊤ : X.Opens) : Set X) from isQuasiSeparated_univ) n
  exact ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eX.symm) ≪≫ₗ
    e ≪≫ₗ eY⟩

end FlatBaseChange

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- The dimension of `Hⁿ(X, M)` does not change under extension of the base field, for a
quasi-coherent sheaf `M` on a quasi-compact quasi-separated scheme over a field.
The coefficients after base change are the canonical pullback
sheaf. -/
theorem finrank_cohomology_pullback_eq_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    Module.finrank K (Cohomology ((Scheme.Modules.pullback g).obj M) n) =
      Module.finrank k (Cohomology M n) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_quasiSeparated H M n
  rw [← e.finrank_eq, Module.finrank_baseChange]

include H in
/-- The cohomology `Hⁿ(X, M)` of a quasi-coherent sheaf stays finite-dimensional under extension of
the base field, on a quasi-compact quasi-separated scheme over a field. -/
theorem finiteDimensional_cohomology_pullback_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) [FiniteDimensional k (Cohomology M n)] :
    FiniteDimensional K (Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_quasiSeparated H M n
  exact Module.Finite.equiv e

include H in
/-- The dimension of `Hⁿ(X, 𝒪_X)` does not change under extension of the base field, on a
quasi-compact quasi-separated scheme over a field, for instance a proper one. -/
theorem finrank_cohomology_trivial_eq_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (n : ℕ) :
    Module.finrank K (Cohomology (InvertibleSheaf.trivial Y).obj n) =
      Module.finrank k (Cohomology (InvertibleSheaf.trivial X).obj n) := by
  let e : (Scheme.Modules.pullback g).obj (InvertibleSheaf.trivial X).obj ≅
      (InvertibleSheaf.trivial Y).obj :=
    (Scheme.Modules.pullback g).mapIso (InvertibleSheaf.trivialObjIsoUnit X) ≪≫
      Scheme.Modules.pullbackObjUnitIso g ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm
  rw [← finrank_cohomology_congr K e n, finrank_cohomology_pullback_eq_of_isPullback H]

include H in
/-- `Hⁿ(X, 𝒪_X)` stays finite-dimensional under extension of the base field, on a quasi-compact
quasi-separated scheme over a field, for instance a proper one. -/
theorem finiteDimensional_cohomology_trivial_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (n : ℕ)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj n)] :
    FiniteDimensional K (Cohomology (InvertibleSheaf.trivial Y).obj n) := by
  let e : (Scheme.Modules.pullback g).obj (InvertibleSheaf.trivial X).obj ≅
      (InvertibleSheaf.trivial Y).obj :=
    (Scheme.Modules.pullback g).mapIso (InvertibleSheaf.trivialObjIsoUnit X) ≪≫
      Scheme.Modules.pullbackObjUnitIso g ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm
  exact (finiteDimensional_cohomology_congr K e n).mp
    (finiteDimensional_cohomology_pullback_of_isPullback H _ n)

include H in
/-- For a proper scheme over a field, `Hⁿ(X, 𝒪_X)` stays finite-dimensional under extension of the
base field. -/
theorem finiteDimensional_cohomology_trivial_of_isPullback_of_isProper
    [IsProper (X ↘ Spec (.of k))] (n : ℕ)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj n)] :
    FiniteDimensional K (Cohomology (InvertibleSheaf.trivial Y).obj n) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  exact finiteDimensional_cohomology_trivial_of_isPullback H n

include H in
/-- The truncated Euler characteristic `∑_{i < n} (-1)ⁱ dim Hⁱ(X, M)` of a quasi-coherent sheaf
does not change under extension of the base field, on a quasi-compact quasi-separated scheme
over a field. -/
theorem eulerCharBelow_pullback_eq_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    eulerCharBelow K Y ((Scheme.Modules.pullback g).obj M) n = eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [eulerCharBelow_succ, eulerCharBelow_succ, ih,
      finrank_cohomology_pullback_eq_of_isPullback H]

end Field

end TauCeti.AlgebraicGeometry

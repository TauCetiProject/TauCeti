/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Smooth connected closed subgroups with equal tangent spaces

A surjective map of coordinate Hopf algebras represents a closed immersion of affine groups.
When both groups are smooth and connected, surjectivity on tangent spaces forces this closed
immersion to be an isomorphism.

The proof uses the conormal module of the surjection. Smoothness makes it finite projective over
the target. Its fibre at the identity is zero, because its split injection into the relative
cotangent space is zero there. Projective-module rank is locally constant, so connectedness of
the target makes the conormal module vanish globally. The kernel is then idempotent; connectedness
of the source and the counit condition force it to be zero.

## Main declaration

* `TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot`: a surjective
  Hopf map between smooth connected affine groups is injective when its conormal space vanishes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a and 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This is the global equality step for the unipotent radical. It upgrades the infinitesimal equality
supplied by the maximal-dimension construction to equality of closed subgroups.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

open TensorProduct

variable {k H K : Type u} [Field k] [CommRing H] [CommRing K]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- The base change to `κ` of the cotangent complex of an extension vanishes when the kernel of the
extension lies in the square of the kernel of `P.Ring → κ`. -/
private theorem lTensor_cotangentComplex_eq_zero {R S κ : Type u} [CommRing R] [CommRing S]
    [CommRing κ] [Algebra R S] [Algebra R κ] [Algebra S κ] [IsScalarTower R S κ]
    (P : Algebra.Extension R S) [Algebra P.Ring κ] [IsScalarTower P.Ring S κ]
    [IsScalarTower R P.Ring κ]
    (h : ∀ x ∈ P.ker, x ∈ RingHom.ker (algebraMap P.Ring κ) ^ 2) :
    P.cotangentComplex.lTensor κ = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a m =>
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P) m
    have hxsq : (x : P.Ring) ∈ RingHom.ker (algebraMap P.Ring κ) ^ 2 := h x x.property
    let xg : RingHom.ker (algebraMap P.Ring κ) :=
      ⟨x, Ideal.pow_le_self two_ne_zero hxsq⟩
    have hxzero : (RingHom.ker (algebraMap P.Ring κ)).toCotangent xg = 0 :=
      (Ideal.toCotangent_eq_zero _ xg).2 hxsq
    have hdx : (1 : κ) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (x : P.Ring) = 0 := by
      simpa only [xg, map_zero, KaehlerDifferential.kerCotangentToTensor_toCotangent] using
        congrArg (KaehlerDifferential.kerCotangentToTensor R P.Ring κ) hxzero
    rw [LinearMap.lTensor_tmul, P.cotangentComplex_mk]
    -- `Extension.CotangentSpace` is an abbreviation for this nested tensor product; exposing
    -- it is necessary to apply the associativity equivalence `cancelBaseChange` below.
    change a ⊗ₜ[S] (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (x : P.Ring)) = 0
    apply (AlgebraTensorModule.cancelBaseChange P.Ring S κ κ
      (KaehlerDifferential R P.Ring)).injective
    simpa only [map_zero, AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_zero] using
      congrArg (a • ·) hdx

/-- A finitely presented flat module over a ring with connected spectrum vanishes if its fibre at
one maximal ideal vanishes, since its rank is locally constant. -/
private theorem subsingleton_of_subsingleton_fiber {R M : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] (p : Ideal R) [p.IsMaximal]
    (h : Subsingleton (p.Fiber M)) : Subsingleton M := by
  have hrank_identity : Module.rankAtStalk (R := R) M
      ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ = 0 := by
    rw [Module.rankAtStalk_eq]
    exact Module.finrank_zero_of_subsingleton
  have hrank : Module.rankAtStalk (R := R) M = 0 := by
    apply funext
    intro q
    simp only [Pi.zero_apply]
    calc
      Module.rankAtStalk M q =
          Module.rankAtStalk M ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ :=
        IsLocallyConstant.apply_eq_of_preconnectedSpace
          (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)) _ _
      _ = 0 := hrank_identity
  exact (Module.rankAtStalk_eq_zero_iff_subsingleton (R := R) (M := M)).mp hrank

/-- The kernel of an extension is idempotent when the cotangent module of the extension vanishes. -/
private theorem isIdempotentElem_ker_of_subsingleton_cotangent {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (P : Algebra.Extension R S) (h : Subsingleton P.Cotangent) :
    IsIdempotentElem P.ker := by
  have hcotangentKer : Subsingleton P.ker.Cotangent := by
    constructor
    intro x y
    apply P.cotangentEquivCotangentKer.symm.injective
    exact Subsingleton.elim _ _
  exact (Ideal.cotangent_subsingleton_iff (I := P.ker)).mp hcotangentKer

/-- A Hopf ideal of a Noetherian Hopf algebra with connected spectrum that lies in the
augmentation ideal and is idempotent is zero. -/
private theorem eq_bot_of_isIdempotentElem_of_le_augmentationIdeal [IsNoetherianRing H]
    [ConnectedSpace (PrimeSpectrum H)] (I : HopfIdeal k H) (hI : IsIdempotentElem I.toIdeal)
    (hI_aug : I.toIdeal ≤ Bialgebra.AugmentationIdeal k H) : I = ⊥ := by
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg I.toIdeal I.toIdeal.fg_of_isNoetherianRing).mp hI
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with rfl | rfl
  · apply HopfIdeal.ext
    intro x
    rw [← mem_toIdeal, ← mem_toIdeal, bot_toIdeal]
    simpa using SetLike.ext_iff.mp hspan x
  · exfalso
    apply RingHom.ker_ne_top (Bialgebra.counitAlgHom k H).toRingHom
    apply top_unique
    intro x _
    apply hI_aug
    rw [hspan]
    simp

/-- The augmentation ideal of a Hopf algebra over a field is a maximal ideal. -/
private theorem isMaximal_augmentationIdeal : (Bialgebra.AugmentationIdeal k K).IsMaximal := by
  dsimp [Bialgebra.AugmentationIdeal]
  exact RingHom.ker_isMaximal_of_surjective _ fun x ↦ ⟨algebraMap k K x, by simp⟩

/-- The kernel of a Hopf map lies in the augmentation ideal of its source. -/
private theorem ker_toIdeal_le_augmentationIdeal (f : H →ₐc[k] K) :
    (HopfIdeal.ker f).toIdeal ≤ Bialgebra.AugmentationIdeal k H := by
  intro x hx
  rw [Bialgebra.AugmentationIdeal, RingHom.mem_ker]
  have hxker : x ∈ RingHom.ker (f : H →ₐ[k] K) := by
    simpa only [HopfIdeal.ker_toIdeal] using hx
  have hcounit := CoalgHomClass.counit_comp_apply f x
  calc
    Coalgebra.counit (R := k) x = Coalgebra.counit (R := k) (f x) := hcounit.symm
    _ = Coalgebra.counit (R := k) 0 := congrArg _ (RingHom.mem_ker.mp hxker)
    _ = 0 := map_zero (Bialgebra.counitAlgHom k K)

/-- Over the residue field at the augmentation ideal of `K`, a Hopf map `f : H → K` has kernel the
augmentation ideal of `H`. -/
private theorem ker_algebraMap_residueField_eq_augmentationIdeal [Algebra H K]
    [(Bialgebra.AugmentationIdeal k K).IsMaximal] (f : H →ₐc[k] K)
    (hf : algebraMap H K = f.toAlgHom.toRingHom) :
    RingHom.ker (algebraMap H (Bialgebra.AugmentationIdeal k K).ResidueField) =
      Bialgebra.AugmentationIdeal k H := by
  ext x
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply H K, Ideal.algebraMap_residueField_eq_zero,
    hf]
  simp only [Bialgebra.AugmentationIdeal, RingHom.mem_ker]
  constructor
  · exact fun hx ↦ (CoalgHomClass.counit_comp_apply f x).symm.trans hx
  · exact fun hx ↦ (CoalgHomClass.counit_comp_apply f x).trans hx

/-- A module that splits off the target of a map whose base change to `κ` is zero has zero base
change to `κ`. -/
private theorem subsingleton_tensor_of_lTensor_eq_zero {R M N κ : Type*} [CommRing R]
    [CommRing κ] [Algebra R κ] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (c : M →ₗ[R] N) (l : N →ₗ[R] M) (hl : l ∘ₗ c = LinearMap.id) (h : c.lTensor κ = 0) :
    Subsingleton (κ ⊗[R] M) := by
  have hinjective : Function.Injective (c.lTensor κ) := by
    intro x y hxy
    have h := congrArg (l.lTensor κ) hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hl,
      LinearMap.lTensor_id, LinearMap.id_apply] using h
  constructor
  intro x y
  apply hinjective
  rw [h]
  rfl

/-- The cotangent module of an extension of `S` with Noetherian total ring is finite over `S`. -/
private theorem finite_cotangent {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) [IsNoetherianRing P.Ring] : Module.Finite S P.Cotangent := by
  have _ : Module.Finite P.Ring P.ker := Module.Finite.of_fg P.ker.fg_of_isNoetherianRing
  have _ : Module.Finite P.Ring P.Cotangent :=
    Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  exact Module.Finite.of_restrictScalars_finite P.Ring S P.Cotangent

/-- A surjective Hopf map between smooth connected affine groups is injective if its conormal
space at the identity vanishes.

Equivalently, a smooth connected closed affine subgroup whose differential is surjective is the
whole ambient group. -/
theorem ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot
    [Algebra.FiniteType k H] (f : H →ₐc[k] K) (hf : Function.Surjective f)
    (hH_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k K))
    (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hconormal : conormalSubspace (HopfIdeal.ker f) = ⊥) : HopfIdeal.ker f = ⊥ := by
  let _ : Algebra H K := f.toAlgHom.toAlgebra
  let _ : IsScalarTower k H K :=
    IsScalarTower.of_algebraMap_eq' f.toAlgHom.comp_algebraMap.symm
  let P : Algebra.Extension k K :=
    { Ring := H
      σ := Function.surjInv hf
      algebraMap_σ := Function.surjInv_eq hf }
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH_smooth
  let _ : Algebra.Smooth k K := (smoothCommHopfAlgProperty_iff _).mp hK_smooth
  let _ : ConnectedSpace (PrimeSpectrum H) := hH_connected
  let _ : ConnectedSpace (PrimeSpectrum K) := hK_connected
  let _ : IsNoetherianRing P.Ring := by
    simpa only [P] using (Algebra.FiniteType.isNoetherianRing k H)
  have hf_algebraMap : algebraMap H K = f.toAlgHom.toRingHom := by
    ext x
    rfl
  have hPker : P.ker = (HopfIdeal.ker f).toIdeal := by
    rw [HopfIdeal.ker_toIdeal]
    exact congrArg RingHom.ker hf_algebraMap
  have hker_aug := ker_toIdeal_le_augmentationIdeal f
  have _ : Module.Finite K P.Cotangent := finite_cotangent P
  obtain ⟨l, hl⟩ := (P.formallySmooth_iff_split_injection).mp
    (inferInstance : Algebra.FormallySmooth k K)
  let _ : Module.Projective K P.CotangentSpace := inferInstance
  let _ : Module.Projective K P.Cotangent :=
    Module.Projective.of_split P.cotangentComplex l hl
  let _ : Module.Flat K P.Cotangent := inferInstance
  let _ : Module.FinitePresentation K P.Cotangent :=
    Module.finitePresentation_of_projective K P.Cotangent
  let p : Ideal K := Bialgebra.AugmentationIdeal k K
  have _ : p.IsMaximal := isMaximal_augmentationIdeal
  let κ := p.ResidueField
  have hbaseChange_zero : P.cotangentComplex.lTensor κ = 0 := by
    refine lTensor_cotangentComplex_eq_zero P fun x hx ↦ ?_
    rw [show RingHom.ker (algebraMap P.Ring κ) = Bialgebra.AugmentationIdeal k H from
      ker_algebraMap_residueField_eq_augmentationIdeal f hf_algebraMap]
    exact (conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal _).mp
      hconormal (hPker ▸ hx)
  have hfiber : Subsingleton (p.Fiber P.Cotangent) :=
    subsingleton_tensor_of_lTensor_eq_zero _ l hl hbaseChange_zero
  have hcotangent : Subsingleton P.Cotangent := subsingleton_of_subsingleton_fiber p hfiber
  have hI_idempotent : IsIdempotentElem (HopfIdeal.ker f).toIdeal := by
    rw [← hPker]
    exact isIdempotentElem_ker_of_subsingleton_cotangent P hcotangent
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  exact eq_bot_of_isIdempotentElem_of_le_augmentationIdeal _ hI_idempotent hker_aug

end HopfIdeal

end

end TauCeti

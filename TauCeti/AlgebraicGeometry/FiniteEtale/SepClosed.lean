/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TotallySplit
import TauCeti.Algebra.Algebra.Pi
import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Relative
import TauCeti.RingTheory.TotallySplit

/-!
# Points and fibres of finite étale schemes over a separably closed field

Every finite étale scheme `X` over a separably closed field `K` splits over `K` itself as the
spectrum of a finite product `Fin n → K` of copies of `K`
(`AlgebraicGeometry.Scheme.Hom.exists_iso_Spec_pi_of_isSepClosed`). Via
`Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` and `Pi.evalAlgHomEquiv`, the underlying space of
`X` is in bijection with `Fin n`, so `X` has finitely many points and their cardinality equals its
rank over `Spec K` (`AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_isSepClosed`).

More generally, for a finite étale morphism `p : E ⟶ S` between finite étale `K`-schemes, the
set-theoretic fibre `{e : E // p e = s}` over each point `s : S` has cardinality `p.finrank s`
(`AlgebraicGeometry.Scheme.Hom.natCard_preimage_eq_finrank_of_isSepClosed`), without assuming
constant rank across the components of `S`.

Finally, once a finite étale `K`-scheme has split over `K`, no further field extension `L / K`
creates new points or identifies existing ones: the base-change projection `X ×_K Spec L ⟶ X` is a
homeomorphism (`AlgebraicGeometry.Scheme.Hom.isHomeomorph_of_isPullback_algebraMap_of_isSepClosed`),
even when `L / K` is inseparable.

## References

* [The Stacks Project, Tag 03QR](https://stacks.math.columbia.edu/tag/03QR): schemes étale over a
  field.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Every finite étale scheme over a separably closed field splits over the ground field.** -/
theorem exists_iso_Spec_pi_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (n : ℕ) (e : X ≅ Spec (.of (Fin n → K))),
      e.hom ≫ Spec.algebraMap K (Fin n → K) = f := by
  obtain ⟨A, ⟨e₀⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨n, ⟨a⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K A.obj
  have hw : e₀.hom.left ≫ f = Spec.algebraMap K A.obj := Over.w e₀.hom
  let e : X ≅ Spec (.of (Fin n → K)) :=
    ((Over.forget _).mapIso e₀).symm ≪≫
      Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.symm.op
  refine ⟨n, e, ?_⟩
  have hmap : Scheme.Spec.map a.toRingEquiv.toCommRingCatIso.symm.op.hom ≫
      Spec.algebraMap K (Fin n → K) = Spec.algebraMap K A.obj := by
    simp only [Iso.op_hom, Iso.symm_hom, Scheme.Spec_map, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext r
    exact a.symm.commutes r
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Over.forget_map, Category.assoc, hmap, ← hw, ← Over.comp_left_assoc, e₀.inv_hom_id,
    Over.id_left, Category.id_comp]

/-- The underlying topological space of a finite étale scheme over a separably closed field is
finite. -/
theorem finite_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] : Finite X := by
  obtain ⟨n, e, -⟩ := f.exists_iso_Spec_pi_of_isSepClosed
  let eqv : Fin n ≃ ↥(Spec (.of (Fin n → K))) :=
    (Pi.evalAlgHomEquiv K (Fin n)).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin n → K))
  exact Finite.of_equiv _ (eqv.trans e.symm.hom.homeomorph.toEquiv)

/-- **The points of a finite étale scheme over a separably closed field number its rank.** -/
theorem natCard_eq_finrank_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card X = f.finrank s := by
  obtain ⟨n, e, he⟩ := f.exists_iso_Spec_pi_of_isSepClosed
  let eqv : Fin n ≃ ↥(Spec (.of (Fin n → K))) :=
    (Pi.evalAlgHomEquiv K (Fin n)).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin n → K))
  have hcard : Nat.card X = n := by
    rw [Nat.card_congr e.hom.homeomorph.toEquiv, ← Nat.card_congr eqv, Nat.card_fin]
  have hef : e.inv ≫ f = Spec.algebraMap K (Fin n → K) := by simp [← he]
  have hfin : (Spec.algebraMap K (Fin n → K)).finrank s = n := by
    rw [Spec.algebraMap, finrank_SpecMap_algebraMap K (Fin n → K) s,
      congrFun Module.rankAtStalk_eq_finrank_of_free s]
    exact (Module.finrank_pi (R := K)).trans (Fintype.card_fin n)
  rw [hcard, ← finrank_comp_left_of_isIso e.inv f, hef, hfin]

/-- **The points in each fibre of a finite étale morphism between finite étale schemes over a
separably closed field number its rank at the base point.** -/
theorem natCard_preimage_eq_finrank_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {S E : Scheme.{u}} (p : E ⟶ S) [IsFinite p] [Etale p]
    (f : S ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : S) :
    Nat.card {e : E // p e = s} = p.finrank s := by
  -- 1. Split both `S` and `E` over `K` to reduce `p` to the spectrum of a `K`-algebra map
  --    `Fin n → K →ₐ[K] Fin m → K`.
  obtain ⟨n, eS, heS⟩ := f.exists_iso_Spec_pi_of_isSepClosed
  obtain ⟨m, eE, heE⟩ := (p ≫ f).exists_iso_Spec_pi_of_isSepClosed
  let p₀ := eE.inv ≫ p ≫ eS.hom
  have hp₀ : p₀ ≫ Spec.algebraMap K (Fin n → K) = Spec.algebraMap K (Fin m → K) := by
    simp only [p₀, Category.assoc, heS, ← heE, Iso.inv_hom_id_assoc]
  have hφ : CommRingCat.ofHom (algebraMap K (Fin n → K)) ≫ Spec.preimage p₀ =
      CommRingCat.ofHom (algebraMap K (Fin m → K)) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, hp₀])
  let φ : (Fin n → K) →ₐ[K] (Fin m → K) :=
    { (Spec.preimage p₀).hom with
      commutes' r := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hφ) r }
  let : Algebra (Fin n → K) (Fin m → K) := φ.toAlgebra
  have : IsScalarTower K (Fin n → K) (Fin m → K) :=
    .of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hφp : Spec.map (CommRingCat.ofHom (algebraMap (Fin n → K) (Fin m → K))) = p₀ :=
    Spec.map_preimage p₀
  have : Module.Finite (Fin n → K) (Fin m → K) := .of_restrictScalars_finite K _ _
  have := Module.projective_of_isSemisimpleRing (Fin n → K) (Fin m → K)
  have : Module.Flat (Fin n → K) (Fin m → K) := inferInstance
  -- 2. Identify the fibre over `s` with `K`-characters of `Fin m → K` extending the character `χ`
  --    corresponding to `eS.hom s`.
  let cN : ((Fin n → K) →ₐ[K] K) ≃ ↥(Spec (.of (Fin n → K))) :=
    Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin n → K)
  let cM : ((Fin m → K) →ₐ[K] K) ≃ ↥(Spec (.of (Fin m → K))) :=
    Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin m → K)
  let χ : (Fin n → K) →ₐ[K] K := cN.symm (eS.hom s)
  have hχ : cN χ = eS.hom s := cN.apply_symm_apply _
  have hcomap (ψ : (Fin m → K) →ₐ[K] K) :
      p₀ (cM ψ) = cN (ψ.comp (IsScalarTower.toAlgHom K (Fin n → K) (Fin m → K))) := by
    rw [← hφp]
    exact PrimeSpectrum.ext (Ideal.ext fun _ ↦ Iff.rfl)
  let fibEquiv : {ψ : (Fin m → K) →ₐ[K] K //
      ψ.comp (IsScalarTower.toAlgHom K (Fin n → K) (Fin m → K)) = χ} ≃ {e : E // p e = s} :=
    (cM.trans (Equiv.ofBijective eE.inv eE.inv.homeomorph.bijective)).subtypeEquiv fun ψ ↦ by
      rw [← cN.injective.eq_iff, hχ, ← hcomap]
      simp only [p₀, Scheme.Hom.comp_apply, Equiv.trans_apply]
      exact eS.hom.homeomorph.injective.eq_iff
  -- 3. Compare the character count with `p.finrank s` via `rankAtStalk`.
  have hrank : Module.rankAtStalk (R := Fin n → K) (Fin m → K)
      ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ = p.finrank s := by
    have hpt : (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : PrimeSpectrum (Fin n → K)) =
        (eS.hom s : PrimeSpectrum (Fin n → K)) := hχ
    rw [hpt, ← finrank_SpecMap_algebraMap (Fin n → K) (Fin m → K) (eS.hom s), hφp]
    have hsq : IsPullback (𝟙 _) (p ≫ eS.hom) p eS.inv :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    exact (congrFun (finrank_comp_left_of_isIso eE.inv (p ≫ eS.hom)) (eS.hom s)).trans <|
      (finrank_of_isPullback _ _ _ _ hsq (eS.hom s)).trans (by simp [← Scheme.Hom.comp_apply])
  rw [← Nat.card_congr fibEquiv, Algebra.IsFiniteSplit.card_algHom_comp_eq_rankAtStalk, hrank]

/-- **Base change of a finite étale scheme over a separably closed field along any field extension
is a homeomorphism.** Because the scheme is already a finite disjoint union of copies of `Spec K`,
extending the field to `L` produces the corresponding disjoint union of copies of `Spec L`. -/
theorem isHomeomorph_of_isPullback_algebraMap_of_isSepClosed
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} [IsFinite f] [Etale f]
    {f' : X' ⟶ Spec (.of L)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    IsHomeomorph g := by
  -- 1. Split `X` over `K` and identify `X'` with `Spec (Fin n → L)` via `L ⊗[K] (Fin n → K)`.
  obtain ⟨n, eX, heX⟩ := f.exists_iso_Spec_pi_of_isSepClosed
  let a : L ⊗[K] (Fin n → K) ≃ₐ[L] (Fin n → L) :=
    (Algebra.TensorProduct.piRight K L L (fun _ : Fin n ↦ K)).trans
      (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.rid K L L)
  let ψ : (Fin n → K) →+* (Fin n → L) :=
    RingHom.pi fun i ↦ (algebraMap K L).comp (Pi.evalRingHom (fun _ : Fin n ↦ K) i)
  have H' : IsPullback (g ≫ eX.hom) f' (Spec.algebraMap K (Fin n → K)) (Spec.algebraMap K L) :=
    H.of_iso (Iso.refl _) eX (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [heX]) (by simp)
  let eX' : X' ≅ Spec (.of (Fin n → L)) :=
    H'.isoPullback ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso K L (Fin n → K) ≪≫
      Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.symm.op
  have hg : eX'.inv ≫ g ≫ eX.hom = Spec.map (CommRingCat.ofHom ψ) := by
    have h1 : (pullbackSpecIso K L (Fin n → K)).inv ≫
        (pullbackSymmetry (Spec.algebraMap K (Fin n → K)) (Spec.algebraMap K L)).inv ≫
        pullback.fst (Spec.algebraMap K (Fin n → K)) (Spec.algebraMap K L) =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
      simp [pullbackSpecIso_inv_snd]
    have ha : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
        a.toRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom ψ :=
      CommRingCat.hom_ext (RingHom.ext fun x ↦ funext fun i ↦ by
        simp [a, ψ, Algebra.TensorProduct.piRight_tmul, Algebra.smul_def])
    simp only [eX', Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv,
      Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc, H'.isoPullback_inv_fst, h1,
      ← Spec.map_comp, ha]
  -- 2. Both `Spec (Fin n → L)` and `Spec (Fin n → K)` are Artinian (hence discrete), and `Spec ψ`
  --    matches the `i`-th coordinate evaluation over `L` with that over `K`.
  have : IsLocallyArtinian (Spec (.of (Fin n → L))) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsLocallyArtinian (Spec (.of (Fin n → K))) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  let eqvL : Fin n ≃ PrimeSpectrum (Fin n → L) :=
    (Pi.evalAlgHomEquiv L (Fin n)).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (Fin n → L))
  let eqvK : Fin n ≃ PrimeSpectrum (Fin n → K) :=
    (Pi.evalAlgHomEquiv K (Fin n)).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin n → K))
  have hcomp₀ (i : Fin n) : PrimeSpectrum.comap ψ (eqvL i) = eqvK i := by
    refine PrimeSpectrum.ext (Ideal.ext fun x ↦ ?_)
    have hL : (eqvL i).asIdeal = RingHom.ker (Pi.evalAlgHom L (fun _ : Fin n ↦ L) i) := by
      rw [Equiv.trans_apply, Algebra.IsFiniteSplit.coe_algHomEquivPrimeSpectrum,
        Pi.evalAlgHomEquiv_apply]
    have hK : (eqvK i).asIdeal = RingHom.ker (Pi.evalAlgHom K (fun _ : Fin n ↦ K) i) := by
      rw [Equiv.trans_apply, Algebra.IsFiniteSplit.coe_algHomEquivPrimeSpectrum,
        Pi.evalAlgHomEquiv_apply]
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hL, hK]
    simp [ψ]
  have hcomp : PrimeSpectrum.comap ψ = eqvL.symm.trans eqvK := by
    funext p
    rw [Equiv.trans_apply, ← hcomp₀, eqvL.apply_symm_apply]
  have hψ : IsHomeomorph (Spec.map (CommRingCat.ofHom ψ)) := by
    let eqv : ↥(Spec (.of (Fin n → L))) ≃ ↥(Spec (.of (Fin n → K))) := eqvL.symm.trans eqvK
    have hmap : (Spec.map (CommRingCat.ofHom ψ) :
        ↥(Spec (.of (Fin n → L))) → ↥(Spec (.of (Fin n → K)))) = eqv := hcomp
    rw [hmap]
    exact eqv.toHomeomorphOfDiscrete.isHomeomorph
  -- 3. Transport the homeomorphism across `eX'` and `eX`.
  have hg' : g = eX'.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ eX.inv := by
    rw [← hg]
    simp
  rw [hg']
  exact (eX.inv.homeomorph.isHomeomorph.comp hψ).comp eX'.hom.homeomorph.isHomeomorph

/-- Base change of a finite étale scheme over a separably closed field along any field extension is
bijective on points. -/
theorem bijective_of_isPullback_algebraMap_of_isSepClosed
    {K L : Type u} [Field K] [IsSepClosed K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} [IsFinite f] [Etale f]
    {f' : X' ⟶ Spec (.of L)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    Function.Bijective g :=
  (isHomeomorph_of_isPullback_algebraMap_of_isSepClosed H).bijective

end AlgebraicGeometry.Scheme.Hom

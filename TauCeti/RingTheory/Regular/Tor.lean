/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.Regular.Category
public import TauCeti.Algebra.Module.Torsion.LTensor
public import TauCeti.Algebra.Module.Torsion.Map
public import TauCeti.CategoryTheory.Monoidal.Tor
public import TauCeti.RingTheory.QuotSMulTop

/-!
# `Tor` against the quotient by a regular element

Let `f` be an element of a commutative ring `R` which is regular on `R`, that is, not a zero
divisor. Multiplication by `f` gives the free resolution `0 → R → R → R ⧸ (f) → 0` of the cyclic
module `R ⧸ (f)`, so for every `R`-module `X`, Mathlib's `Tor`, which derives the tensor product
in its second variable, is computed by the two-term complex `X → X` of multiplication by `f`:

* `Tor₁^R(X, R ⧸ (f))` is the `f`-torsion `X[f] = {x | f • x = 0}` of `X`
  (`ModuleCat.torOneQuotientSpanSingletonIso`), naturally in `X`
  (`ModuleCat.Tor_map_app_comp_torOneQuotientSpanSingletonIso_hom`);
* `Torₙ^R(X, R ⧸ (f))` vanishes for `n ≥ 2` (`ModuleCat.isZero_Tor_add_two_quotientSpanSingleton`).

In particular, when `f` kills `X`, `Tor₁^R(X, R ⧸ (f))` is `X` itself
(`ModuleCat.torOneQuotientSpanSingletonIsoOfIsTorsionBy`). For `X = R ⧸ (f)` this is the
classical computation `Tor₁^R(R ⧸ (f), R ⧸ (f)) ≅ R ⧸ (f)`
(`ModuleCat.torOneQuotientSpanSingletonSelfIso`): the class lost when one forms the homology of
the resolution before reducing modulo `f`.

This is how `Tor` measures the failure of a nonflat change of coefficients to commute with
homology. The complex `R → R` of multiplication by `f` has homology `R ⧸ (f)` in degree zero only,
but after tensoring with `X` it has homology `X ⧸ f X ≅ X ⊗ R ⧸ (f)` in degree zero and `X[f]` in
degree one, and the degree-one class is `Tor₁^R(X, R ⧸ (f))`. Twisted Floer complexes, with
coefficients in a group ring, change their coefficients along the augmentation in exactly this
way.

## Main results

* `ModuleCat.torOneQuotientSpanSingletonIso`: `Tor₁^R(X, R ⧸ (f)) ≅ X[f]` for `f` regular.
* `ModuleCat.Tor_map_app_comp_torOneQuotientSpanSingletonIso_hom`: its naturality in `X`.
* `ModuleCat.isZero_Tor_add_two_quotientSpanSingleton`: `Torₙ^R(X, R ⧸ (f)) = 0` for `n ≥ 2`.
* `ModuleCat.torOneQuotientSpanSingletonIsoOfIsTorsionBy`: `Tor₁^R(X, R ⧸ (f)) ≅ X` when `f`
  kills `X`.
* `ModuleCat.torOneQuotientSpanSingletonSelfIso`: `Tor₁^R(R ⧸ (f), R ⧸ (f)) ≅ R ⧸ (f)`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 3.1 (`Tor` of a cyclic module
  `R ⧸ (f)` for a nonzerodivisor `f`, computed from the resolution by multiplication by `f`).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Submodule

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R] {f : R}

private instance (f : R) : Projective (smulShortComplex (of R R) f).X₁ :=
  projective_of_free (Module.Free.chooseBasis R R)

private instance (f : R) : Projective (smulShortComplex (of R R) f).X₂ :=
  projective_of_free (Module.Free.chooseBasis R R)

/-- For `f` regular on `R`, multiplication by `f` gives the short exact sequence
`0 → R → R → R ⧸ f • R → 0`. -/
private theorem shortExact_smulShortComplex (hf : IsSMulRegular R f) :
    (smulShortComplex (of R R) f).ShortExact :=
  IsSMulRegular.smulShortComplex_shortExact (M := of R R) hf

/-- `QuotSMulTop.equivQuotSpanSingleton` with its domain written as the last object of
`ModuleCat.smulShortComplex`, so that it composes syntactically with
`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernel` in the rewrites below. -/
private def quotSMulTopIso (f : R) :
    (smulShortComplex (of R R) f).X₃ ≅ of R (R ⧸ Ideal.span {f}) :=
  (QuotSMulTop.equivQuotSpanSingleton f).toModuleIso

private theorem kerLTensorLsmulEquiv_hom_subtype (X : ModuleCat.{u} R) (f : R) :
    (TauCeti.kerLTensorLsmulEquiv X f).toModuleIso.hom ≫ ofHom (torsionBy R X f).subtype =
      ofHom (LinearMap.ker ((LinearMap.lsmul R R f).lTensor X)).subtype ≫
        ofHom (TensorProduct.rid R X).toLinearMap :=
  hom_ext <| LinearMap.ext <| TauCeti.coe_kerLTensorLsmulEquiv_apply X f

/-- **`Tor₁` against `R ⧸ (f)`.** For an element `f` of `R` regular on `R`, `Tor₁^R(X, R ⧸ (f))`
is the `f`-torsion `X[f]` of `X`. -/
def torOneQuotientSpanSingletonIso (hf : IsSMulRegular R f) (X : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj X).obj (of R (R ⧸ Ideal.span {f})) ≅
      of R (torsionBy R X f) :=
  ((Tor (ModuleCat.{u} R) 1).obj X).mapIso (quotSMulTopIso f).symm ≪≫
    (shortExact_smulShortComplex hf).torOneIsoKernel X ≪≫ kernelIsoKer _ ≪≫
      (TauCeti.kerLTensorLsmulEquiv X f).toModuleIso

/-- The identification `Tor₁^R(X, R ⧸ (f)) ≅ X[f]` is natural in `X`: a map `g : X ⟶ Y` acts on
`Tor₁` as it acts on `f`-torsion, by restriction (`TauCeti.torsionByMap`). -/
@[reassoc]
theorem Tor_map_app_comp_torOneQuotientSpanSingletonIso_hom (hf : IsSMulRegular R f)
    {X Y : ModuleCat.{u} R} (g : X ⟶ Y) :
    ((Tor (ModuleCat.{u} R) 1).map g).app (of R (R ⧸ Ideal.span {f})) ≫
        (torOneQuotientSpanSingletonIso hf Y).hom =
      (torOneQuotientSpanSingletonIso hf X).hom ≫
        ofHom (TauCeti.torsionByMap f g.hom) := by
  simp only [torOneQuotientSpanSingletonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [← NatTrans.naturality_assoc,
    (shortExact_smulShortComplex hf).Tor_map_app_comp_torOneIsoKernel_hom_assoc]
  congr 2
  rw [← cancel_epi (kernelIsoKer _).inv, ← cancel_mono (ofHom (torsionBy R Y f).subtype)]
  have hrid : g ▷ (smulShortComplex (of R R) f).X₁ ≫ ofHom (TensorProduct.rid R Y).toLinearMap =
      ofHom (TensorProduct.rid R X).toLinearMap ≫ g :=
    ModuleCat.hom_ext <| TensorProduct.ext' fun x (r : R) =>
      (TensorProduct.rid_tmul (g x) r).trans (map_smul g.hom r x).symm
  have hrestrict : ofHom (TauCeti.torsionByMap f g.hom) ≫ ofHom (torsionBy R Y f).subtype =
      ofHom (torsionBy R X f).subtype ≫ g :=
    ModuleCat.hom_ext <| LinearMap.ext fun _ => TauCeti.coe_torsionByMap_apply f g.hom _
  -- The kernels of `X ◁ S.f` and `Y ◁ S.f` as kernels of the linear maps `x ⊗ r ↦ x ⊗ f r`.
  have hY : (kernelIsoKer (Y ◁ (smulShortComplex (of R R) f).f)).hom ≫
      ofHom (LinearMap.ker ((LinearMap.lsmul R R f).lTensor Y)).subtype =
      kernel.ι (Y ◁ (smulShortComplex (of R R) f).f) :=
    kernelIsoKer_hom_ker_subtype _
  have hX : (kernelIsoKer (X ◁ (smulShortComplex (of R R) f).f)).inv ≫
      kernel.ι (X ◁ (smulShortComplex (of R R) f).f) =
      ofHom (LinearMap.ker ((LinearMap.lsmul R R f).lTensor X)).subtype :=
    kernelIsoKer_inv_kernel_ι _
  simp only [Category.assoc, hrestrict, kerLTensorLsmulEquiv_hom_subtype,
    reassoc_of% kerLTensorLsmulEquiv_hom_subtype,
    reassoc_of% hY, kernel.lift_ι_assoc, hrid, reassoc_of% hX, Iso.inv_hom_id_assoc]

/-- `Torₙ^R(X, R ⧸ (f))` vanishes for `n ≥ 2` when `f` is regular on `R`. -/
theorem isZero_Tor_add_two_quotientSpanSingleton (hf : IsSMulRegular R f)
    (X : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 2)).obj X).obj (of R (R ⧸ Ideal.span {f}))) :=
  ((shortExact_smulShortComplex hf).isZero_Tor_add_two X n).of_iso
    (((Tor (ModuleCat.{u} R) (n + 2)).obj X).mapIso (quotSMulTopIso f).symm)

/-- If `f` is regular on `R` and kills `X`, then `Tor₁^R(X, R ⧸ (f))` is `X`. This applies to
`X = R ⧸ (f)`. -/
def torOneQuotientSpanSingletonIsoOfIsTorsionBy (hf : IsSMulRegular R f) {X : ModuleCat.{u} R}
    (hX : Module.IsTorsionBy R X f) :
    ((Tor (ModuleCat.{u} R) 1).obj X).obj (of R (R ⧸ Ideal.span {f})) ≅ X :=
  torOneQuotientSpanSingletonIso hf X ≪≫
    ((LinearEquiv.ofEq _ _ ((Module.isTorsionBy_iff_torsionBy_eq_top f).mp hX)).trans
      Submodule.topEquiv).toModuleIso

/-- **`Tor₁^R(R ⧸ (f), R ⧸ (f)) ≅ R ⧸ (f)`** for `f` regular on `R`: the kernel of multiplication by
`f` on `R ⧸ (f)` is everything. -/
def torOneQuotientSpanSingletonSelfIso (hf : IsSMulRegular R f) :
    ((Tor (ModuleCat.{u} R) 1).obj (of R (R ⧸ Ideal.span {f}))).obj
      (of R (R ⧸ Ideal.span {f})) ≅ of R (R ⧸ Ideal.span {f}) :=
  torOneQuotientSpanSingletonIsoOfIsTorsionBy hf <|
    (Module.isTorsionBy_quotient_iff _ f).mpr fun x =>
      Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self f)

end ModuleCat

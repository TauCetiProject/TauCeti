/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Rank
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.Idempotents.Product
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.Topology.LocallyConstant.ClopenRingHom
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.RingTheory.Spectrum.Prime.Idempotent
import TauCeti.Topology.LocallyConstant.CharFn

/-!
# The locally constant rank on projective `K₀` and its section

Let `R` be a commutative ring and `K₀(R)` the split Grothendieck group of finitely generated
projective `R`-modules, a commutative ring under the tensor product. A finitely generated
projective module `P` has a rank at every prime `p`, the rank of the free `Rₚ`-module `Pₚ`
(`Module.rankAtStalk`), and this rank is a locally constant function on `Spec R`. It is additive
on direct sums and multiplicative on tensor products, so it induces a ring homomorphism

  `rank : K₀(R) →+* H(R)`, `H(R) = LocallyConstant (Spec R) ℤ`.

No connectedness is assumed: on a disconnected spectrum the rank of a projective module need not
be constant, and `H(R)` is larger than `ℤ`.

The rank homomorphism is split surjective. A clopen subset `U ⊆ Spec R` is the basic open set of
a unique idempotent `e_U` of `R`, and the module `P_U = R ⧸ (1 - e_U) ≅ R e_U` is finitely
generated projective of rank the characteristic function `χ_U` of `U`. These classes satisfy
`[P_⊤] = 1`, `[P_{U ∩ V}] = [P_U] [P_V]` and `[P_{Uᶜ}] = 1 - [P_U]`, the last because
`R ≅ P_U × P_{Uᶜ}`. Since the locally constant integer functions on the compact space `Spec R` are
the integer combinations of characteristic functions of clopen sets, there is a unique ring
homomorphism

  `rankSection : H(R) →+* K₀(R)`, `χ_U ↦ [P_U]`,

and `rank ∘ rankSection = id`. Thus the rank is a split surjection of rings, whose kernel is the
reduced `K₀` of `R`.

The rank is natural under extension of scalars along any ring homomorphism `f : R →+* S`: the
extended module `S ⊗_R P` has rank at a prime `q` of `S` the rank of `P` at `f⁻¹ q`, so the rank
of the image of a class under `K₀(f)` is the pullback of its rank along `Spec S → Spec R`.

The rank section is natural under extension of scalars along any ring homomorphism
`f : R →+* S`. The idempotent of the preimage of `U` under `Spec f : Spec S → Spec R` is `f e_U`,
so `S ⊗_R P_U ≅ S ⧸ (1 - f e_U)` is the module of that preimage, and hence the extension of
`rankSection g` along `f` is the rank section of the pullback `g ∘ Spec f`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rank`: the rank homomorphism
  `K₀(R) →+* LocallyConstant (PrimeSpectrum R) ℤ`.
* `TauCeti.FiniteProjectiveModules.clopenProjective`: the finitely generated projective module
  `P_U = R ⧸ (1 - e_U)` of a clopen subset `U` of the prime spectrum.
* `TauCeti.FiniteProjectiveModules.rankSection`: the ring homomorphism
  `LocallyConstant (PrimeSpectrum R) ℤ →+* K₀(R)` sending `χ_U` to `[P_U]`.

## Main results

* `TauCeti.FiniteProjectiveModules.rank_of`: the rank of `[P]` at `p` is the rank of `Pₚ`.
* `TauCeti.FiniteProjectiveModules.rank_of_clopenProjective`: `P_U` has rank `χ_U`.
* `TauCeti.FiniteProjectiveModules.of_clopenProjective_top`,
  `TauCeti.FiniteProjectiveModules.of_clopenProjective_inf` and
  `TauCeti.FiniteProjectiveModules.of_clopenProjective_compl`: the classes `[P_U]` form a
  homomorphism of Boolean algebras from the clopen sets to the idempotents of `K₀(R)`.
* `TauCeti.FiniteProjectiveModules.rankSection_apply`: the rank section sends `f` to
  `∑ n [P_{f⁻¹{n}}]`.
* `TauCeti.FiniteProjectiveModules.rank_rankSection`: the rank is a retraction of the section, so
  `rank` is surjective and `rankSection` is injective.
* `TauCeti.FiniteProjectiveModules.rank_map`: the rank commutes with extension of scalars.
* `TauCeti.FiniteProjectiveModules.map_of_clopenProjective`: extension of scalars along `f` sends
  `[P_U]` to the class of the module of the preimage of `U` under `Spec f`.
* `TauCeti.FiniteProjectiveModules.map_rankSection`: the rank section commutes with extension of
  scalars.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, the rank
  `rank : K₀(R) → H₀(R)` and its splitting, pp. 71–72 (Definition 2.3 and Lemma 2.3.1 there).
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory TopologicalSpace PrimeSpectrum

universe u

namespace FiniteProjectiveModules

variable (R : Type u) [CommRing R]

/-! ### The rank homomorphism -/

/-- The stalk rank of a finitely generated projective module, as a locally constant integer
function on the prime spectrum. It is invariant under isomorphism and additive on biproducts. -/
private noncomputable def rankInvariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory
      (LocallyConstant (PrimeSpectrum R) ℤ) where
  obj P :=
    have := Module.finitePresentation_of_projective R P.obj
    ⟨fun p ↦ (Module.rankAtStalk P.obj p : ℤ), Module.isLocallyConstant_rankAtStalk.comp _⟩
  map_iso P Q e := by
    ext p
    simp only [LocallyConstant.coe_mk, Nat.cast_inj]
    exact congr_fun (Module.rankAtStalk_eq_of_equiv
      ((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv) p
  map_biprod P Q := by
    ext p
    simp [Module.rankAtStalk_eq_of_equiv (biprodLinearEquiv P Q), Module.rankAtStalk_prod]

/-- **The rank homomorphism** `K₀(R) →+* H(R)`. It sends the class of a finitely generated
projective module `P` to its rank function `p ↦ rank_{Rₚ} Pₚ`, a locally constant integer
function on `Spec R`. -/
noncomputable def rank :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  SplitK0.liftRingHom (rankInvariant R)
    (by
      ext p
      have := p.nontrivial
      simp only [rankInvariant, tensorUnit_obj, LocallyConstant.coe_mk, LocallyConstant.coe_one,
        Pi.one_apply, Nat.cast_eq_one, Module.rankAtStalk_eq_finrank_of_free]
      exact Module.finrank_self R)
    (fun P Q ↦ by
      ext p
      simp only [rankInvariant, tensorObj_obj, LocallyConstant.coe_mk, LocallyConstant.coe_mul,
        Pi.mul_apply]
      exact_mod_cast congr_fun (Module.rankAtStalk_tensorProduct Q.obj) p)

/-- The rank of the class of `P` at a prime `p` is the rank of the free `Rₚ`-module `Pₚ`. -/
@[simp]
theorem rank_of (P : (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rank R (SplitK0.of.{u} P) p = Module.rankAtStalk P.obj p := by
  simp [rank, rankInvariant]

/-! ### The projective module of a clopen set -/

/-- The finitely generated projective module `P_U = R ⧸ (1 - e_U)` of a clopen subset `U` of
`Spec R`, where `e_U` is the idempotent whose basic open set is `U`. It is isomorphic to the ideal
`R e_U`, and its rank is the characteristic function of `U`. -/
noncomputable def clopenProjective (U : Clopens (PrimeSpectrum R)) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (R ⧸ Ideal.span {1 - (isIdempotentElemEquivClopens.symm U).val}),
    finiteProjectiveModules_iff.mpr ⟨inferInstance,
      Module.Projective.quotient_span_singleton_of_isIdempotentElem
        (isIdempotentElemEquivClopens.symm U).prop.one_sub⟩⟩

/-- The underlying module of `P_U` is `R ⧸ (1 - e_U)`. -/
theorem clopenProjective_obj (U : Clopens (PrimeSpectrum R)) :
    (clopenProjective R U).obj =
      ModuleCat.of R (R ⧸ Ideal.span {1 - (isIdempotentElemEquivClopens.symm U).val}) :=
  (rfl)

/-- The module `P_U` has rank the characteristic function of `U`: rank one at the primes of `U`
and rank zero elsewhere. -/
@[simp]
theorem rank_of_clopenProjective (U : Clopens (PrimeSpectrum R)) :
    rank R (SplitK0.of.{u} (clopenProjective R U)) = LocallyConstant.charFn ℤ U.isClopen := by
  set e := isIdempotentElemEquivClopens.symm U
  ext p
  -- The underlying module of `P_U` is `R ⧸ (1 - e)`.
  have hobj : Module.rankAtStalk (clopenProjective R U).obj p =
      Module.rankAtStalk (R ⧸ Ideal.span {1 - e.val}) p :=
    congr_fun (Module.rankAtStalk_eq_of_equiv (eqToIso (clopenProjective_obj R U)).toLinearEquiv) p
  -- `R ⧸ (1 - e)` has rank one exactly on the basic open set of `e`, which is `U`.
  have hU : e.val ∈ p.asIdeal ↔ p ∉ U := by
    rw [iff_not_comm, ← mem_basicOpen, basicOpen_isIdempotentElemEquivClopens_symm]
    rfl
  rw [rank_of, hobj, Module.rankAtStalk_quotient_span_one_sub e.prop, LocallyConstant.coe_charFn]
  split_ifs with h
  · simp [hU.mp h]
  · simp [not_not.mp (hU.not.mp h)]

/-- The projective module of the whole spectrum is `R`: `[P_⊤] = 1`. -/
@[simp]
theorem of_clopenProjective_top : SplitK0.of.{u} (clopenProjective R ⊤) = 1 := by
  rw [SplitK0.one_def]
  -- The isomorphism is built on underlying modules: `P_⊤` is `R ⧸ (1 - 1)` by
  -- `clopenProjective_obj`, and the unit is `R` by `tensorUnit_obj`.
  refine SplitK0.of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (eqToIso (clopenProjective_obj R ⊤) ≪≫
      LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ ?_) ≪≫
      eqToIso (tensorUnit_obj R).symm))
  rw [isIdempotentElemEquivClopens_symm_top, sub_self, Ideal.span_singleton_eq_bot]

/-- The projective module of an intersection is the tensor product: `[P_{U ∩ V}] = [P_U] [P_V]`,
since `R ⧸ (1 - e) ⊗ R ⧸ (1 - f) ≅ R ⧸ (1 - e f)` for idempotents `e` and `f`. -/
theorem of_clopenProjective_inf (U V : Clopens (PrimeSpectrum R)) :
    SplitK0.of.{u} (clopenProjective R (U ⊓ V)) =
      SplitK0.of.{u} (clopenProjective R U) * SplitK0.of.{u} (clopenProjective R V) := by
  set e := isIdempotentElemEquivClopens.symm U
  set f := isIdempotentElemEquivClopens.symm V
  -- The ideals `(1 - e)` and `(1 - f)` generate `(1 - e f)`.
  have hspan : Ideal.span {1 - e.val} ⊔ Ideal.span {1 - f.val} =
      Ideal.span {1 - (isIdempotentElemEquivClopens.symm (U ⊓ V)).val} := by
    rw [isIdempotentElemEquivClopens_symm_inf]
    exact f.prop.span_one_sub_sup_span_one_sub (.all _ _)
  rw [SplitK0.of_mul_of]
  -- The isomorphism is built on underlying modules: `P_U` is `R ⧸ (1 - e)` by
  -- `clopenProjective_obj`, and the tensor product is that of modules by `tensorObj_obj`.
  exact SplitK0.of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (eqToIso (clopenProjective_obj R (U ⊓ V)) ≪≫
      LinearEquiv.toModuleIso ((Submodule.quotEquivOfEq _ _ hspan).symm ≪≫ₗ
        (TensorProduct.quotTensorQuotEquivQuotSup _ _).symm ≪≫ₗ
        TensorProduct.congr (eqToIso (clopenProjective_obj R U)).toLinearEquiv.symm
          (eqToIso (clopenProjective_obj R V)).toLinearEquiv.symm) ≪≫
      eqToIso (tensorObj_obj R _ _).symm))

/-- The projective modules of complementary clopen sets add up to `R`:
`[P_{Uᶜ}] = 1 - [P_U]`, since `R ≅ R ⧸ (1 - e) × R ⧸ (e)` for an idempotent `e`. -/
theorem of_clopenProjective_compl (U : Clopens (PrimeSpectrum R)) :
    SplitK0.of.{u} (clopenProjective R Uᶜ) = 1 - SplitK0.of.{u} (clopenProjective R U) := by
  set e := isIdempotentElemEquivClopens.symm U
  rw [eq_sub_iff_add_eq', SplitK0.one_def]
  refine (SplitK0.of_eq_add_of_linearEquiv_prod ?_).symm
  -- `R ≅ R ⧸ (1 - e) × R ⧸ (e)`, carried to the underlying modules by `tensorUnit_obj` and
  -- `clopenProjective_obj`.
  exact (eqToIso (tensorUnit_obj R)).toLinearEquiv ≪≫ₗ
    (AlgEquiv.prodQuotientOfIsIdempotentElem R e.prop.one_sub e.prop (sub_add_cancel 1 e.val)
      e.prop.one_sub_mul_self).toLinearEquiv ≪≫ₗ
    (eqToIso (clopenProjective_obj R U)).toLinearEquiv.symm.prodCongr
      (Submodule.quotEquivOfEq _ _
        (by rw [isIdempotentElemEquivClopens_symm_compl, sub_sub_cancel]) ≪≫ₗ
        (eqToIso (clopenProjective_obj R Uᶜ)).toLinearEquiv.symm)

/-! ### The rank section -/

/-- **The rank section** `H(R) →+* K₀(R)`: the ring homomorphism sending the characteristic
function of a clopen set `U ⊆ Spec R` to the class of `P_U = R ⧸ (1 - e_U)`, and a locally constant
function `f` to `∑ n [P_{f⁻¹{n}}]`. It is the only ring homomorphism with these values on
characteristic functions, by `LocallyConstant.ringHom_ext_charFn`. -/
noncomputable def rankSection :
    LocallyConstant (PrimeSpectrum R) ℤ →+*
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  LocallyConstant.ringHomOfClopens (c := fun U ↦ SplitK0.of.{u} (clopenProjective R U))
    (of_clopenProjective_top R) (of_clopenProjective_inf R) (of_clopenProjective_compl R)

/-- The rank section sends the characteristic function of `U` to the class of `P_U`. -/
@[simp]
theorem rankSection_charFn (U : Clopens (PrimeSpectrum R)) :
    rankSection R (LocallyConstant.charFn ℤ U.isClopen) = SplitK0.of.{u} (clopenProjective R U) :=
  LocallyConstant.ringHomOfClopens_charFn _ _ _ U

/-- The rank section sends a locally constant function `f` to `∑ n [P_{f⁻¹{n}}]`, summed over any
finite set of integers containing the values of `f`. -/
theorem rankSection_apply (f : LocallyConstant (PrimeSpectrum R) ℤ) {s : Finset ℤ}
    (hs : Set.range f ⊆ s) :
    rankSection R f = ∑ n ∈ s, n • SplitK0.of.{u} (clopenProjective R (f.fiberClopens n)) :=
  LocallyConstant.ringHomOfClopens_apply _ _ _ f hs

/-- **The rank is split surjective.** The rank section is a right inverse of the rank: the class
`rankSection f` has rank `f`. -/
@[simp]
theorem rank_rankSection (f : LocallyConstant (PrimeSpectrum R) ℤ) :
    rank R (rankSection R f) = f := by
  have h : (rank R).comp (rankSection R) = RingHom.id _ :=
    LocallyConstant.ringHom_ext_charFn fun U ↦ by simp
  exact DFunLike.congr_fun h f

/-- Every locally constant integer function on `Spec R` is the rank of a class in `K₀(R)`. -/
theorem rank_surjective : Function.Surjective (rank R) :=
  fun f ↦ ⟨rankSection R f, rank_rankSection R f⟩

/-- The rank section is injective. -/
theorem rankSection_injective : Function.Injective (rankSection R) :=
  Function.LeftInverse.injective (rank_rankSection R)

/-! ### Naturality under extension of scalars -/

variable {R} {S : Type u} [CommRing S]

/-- **The rank is natural under extension of scalars.** Along a ring homomorphism `f : R →+* S`,
the rank of the extended class `[S ⊗_R P]` at a prime `q` of `S` is the rank of `[P]` at the
contracted prime `f⁻¹ q`; that is, `rank ∘ K₀(f)` is the pullback of the rank along
`Spec f : Spec S → Spec R`. -/
@[simp]
theorem rank_map (f : R →+* S) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rank S (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      (rank R x).comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ := by
  suffices h : (rank S).toAddMonoidHom.comp
      (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars) =
      (LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).toAddMonoidHom.comp
        (rank R).toAddMonoidHom from DFunLike.congr_fun h x
  refine SplitK0.hom_ext fun P ↦ ?_
  let := f.toAlgebra
  -- The balanced extension of `P` along `f` is Mathlib's base change `S ⊗[R] P`.
  let e : (f.finiteProjectiveModulesExtendScalars.obj P).obj ≃ₗ[S] TensorProduct R S P.obj :=
    (f.finiteProjectiveModulesExtendScalarsCompιIso.app P ≪≫
      (BalancedExtension.extendScalarsIso f).app P.obj ≪≫
      ModuleCat.extendScalarsAlgebraMapIso P.obj).toLinearEquiv
  ext q
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass,
    Function.comp_apply, SplitK0.map_of, rank_of, LocallyConstant.comapRingHom_apply_apply,
    ContinuousMap.coe_mk, Nat.cast_inj]
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange,
    RingHom.algebraMap_toAlgebra]

/-- **Extension of scalars pulls back the clopen projective modules.** Along a ring homomorphism
`f : R →+* S`, the extension `S ⊗_R P_U` of the module of a clopen subset `U` of `Spec R` is the
module of its preimage under `Spec f : Spec S → Spec R`: both are `S ⧸ (1 - f e_U)`, since the
idempotent of the preimage is `f e_U` (`PrimeSpectrum.isIdempotentElemEquivClopens_symm_preimage`).
-/
theorem map_of_clopenProjective (f : R →+* S) (U : Clopens (PrimeSpectrum R)) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars
        (SplitK0.of.{u} (clopenProjective R U)) =
      SplitK0.of.{u} (clopenProjective S
        ⟨PrimeSpectrum.comap f ⁻¹' U, U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩) := by
  let := f.toAlgebra
  set e := isIdempotentElemEquivClopens.symm U
  -- The extended ideal of `(1 - e_U)` is `(1 - f e_U)`, the ideal of the preimage.
  have hspan : (Ideal.span {1 - e.val}).map (algebraMap R S) =
      Ideal.span {1 - (isIdempotentElemEquivClopens.symm
        ⟨PrimeSpectrum.comap f ⁻¹' U, U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩).val}
      := by
    rw [isIdempotentElemEquivClopens_symm_preimage, Ideal.map_span, Set.image_singleton, map_sub,
      map_one, RingHom.algebraMap_toAlgebra]
  -- The balanced extension of `P_U` is Mathlib's base change `S ⊗[R] (R ⧸ (1 - e_U))`, which is
  -- `S ⧸ (1 - f e_U)` by `Ideal.quotMapEquivTensorQuot`.
  exact (SplitK0.map_of _ _).trans (SplitK0.of_extendScalars_obj
    (((BalancedExtension.extendScalarsIso f).app _ ≪≫
        ModuleCat.extendScalarsAlgebraMapIso _).toLinearEquiv ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (eqToIso (clopenProjective_obj R U)).toLinearEquiv ≪≫ₗ
      (Ideal.quotMapEquivTensorQuot S).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hspan ≪≫ₗ
      (eqToIso (clopenProjective_obj S _)).toLinearEquiv.symm))

/-- **The rank section is natural under extension of scalars.** Along a ring homomorphism
`f : R →+* S`, extending the class `rankSection g` of a locally constant function `g` on `Spec R`
gives the rank section of its pullback `g ∘ Spec f` along `Spec f : Spec S → Spec R`. -/
@[simp]
theorem map_rankSection (f : R →+* S) (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (rankSection R g) =
      rankSection S (g.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) := by
  suffices h : (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars).comp
      (rankSection R).toAddMonoidHom = (rankSection S).toAddMonoidHom.comp
        (LocallyConstant.comapAddMonoidHom
          ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) from
    DFunLike.congr_fun h g
  refine LocallyConstant.addMonoidHom_ext_charFn fun U ↦ ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, LocallyConstant.comapAddMonoidHom_apply,
    LocallyConstant.comap_charFn, rankSection_charFn]
  exact (map_of_clopenProjective f U).trans (rankSection_charFn S _).symm

end FiniteProjectiveModules

end TauCeti

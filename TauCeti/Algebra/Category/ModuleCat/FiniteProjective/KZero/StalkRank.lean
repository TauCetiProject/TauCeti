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
public import TauCeti.RingTheory.Ideal.Pure
public import TauCeti.Topology.LocallyConstant.ClopenRingHom

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
* `TauCeti.FiniteProjectiveModules.rank_rankSection`: the rank is a retraction of the section, so
  `rank` is surjective and `rankSection` is injective.

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
      simp only [rankInvariant, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply,
        Nat.cast_eq_one, Module.rankAtStalk_eq_finrank_of_free]
      exact Module.finrank_self R)
    (fun P Q ↦ by
      ext p
      simp only [rankInvariant, LocallyConstant.coe_mk, LocallyConstant.coe_mul, Pi.mul_apply]
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
  set e : R := (isIdempotentElemEquivClopens.symm U).val
  have := Module.Projective.quotient_span_singleton_of_isIdempotentElem
    (isIdempotentElemEquivClopens.symm U).prop.one_sub
  ext p
  -- `R ⧸ (1 - e)` is a finite flat `R`-algebra with surjective structure map, so its rank is at
  -- most one, and positive exactly on the image of its spectrum, which is `V(1 - e) = U`.
  have hle : Module.rankAtStalk (R ⧸ Ideal.span {1 - e}) p ≤ 1 :=
    Module.rankAtStalk_le_one_iff_surjective.mpr Ideal.Quotient.mk_surjective p
  have hpos : 0 < Module.rankAtStalk (R ⧸ Ideal.span {1 - e}) p ↔ p ∈ U := by
    rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap, Ideal.Quotient.algebraMap_eq,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zeroLocus_span,
      ← basicOpen_eq_zeroLocus_of_isIdempotentElem _ (isIdempotentElemEquivClopens.symm U).prop,
      basicOpen_isIdempotentElemEquivClopens_symm]
    simp
  -- The underlying module of `P_U` is `R ⧸ (1 - e)` by definition.
  have hobj : Module.rankAtStalk (clopenProjective R U).obj p =
      Module.rankAtStalk (R ⧸ Ideal.span {1 - e}) p := rfl
  rw [rank_of, hobj, LocallyConstant.coe_charFn]
  by_cases hp : p ∈ U
  · rw [Set.indicator_of_mem hp, Pi.one_apply]
    have := hpos.mpr hp
    omega
  · rw [Set.indicator_of_notMem hp]
    have := mt hpos.mp hp
    omega

/-- The projective module of the whole spectrum is `R`: `[P_⊤] = 1`. -/
@[simp]
theorem of_clopenProjective_top : SplitK0.of.{u} (clopenProjective R ⊤) = 1 := by
  rw [SplitK0.one_def]
  refine SplitK0.of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ ?_)))
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
    refine le_antisymm (sup_le ?_ ?_) (Ideal.span_singleton_le_iff_mem _ |>.mpr ?_)
    · exact Ideal.span_singleton_le_span_singleton.mpr
        ⟨1 - e.val, by linear_combination (-f.val) * e.prop.eq⟩
    · exact Ideal.span_singleton_le_span_singleton.mpr
        ⟨1 - f.val, by linear_combination (-e.val) * f.prop.eq⟩
    · have h : 1 - e.val * f.val = (1 - e.val) + e.val * (1 - f.val) := by ring
      rw [h]
      exact add_mem (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  rw [SplitK0.of_mul_of]
  exact SplitK0.of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (LinearEquiv.toModuleIso ((Submodule.quotEquivOfEq _ _ hspan).symm ≪≫ₗ
      (TensorProduct.quotTensorQuotEquivQuotSup _ _).symm)))

/-- The projective modules of complementary clopen sets add up to `R`:
`[P_{Uᶜ}] = 1 - [P_U]`, since `R ≅ R ⧸ (1 - e) × R ⧸ (e)` for an idempotent `e`. -/
theorem of_clopenProjective_compl (U : Clopens (PrimeSpectrum R)) :
    SplitK0.of.{u} (clopenProjective R Uᶜ) = 1 - SplitK0.of.{u} (clopenProjective R U) := by
  set e := isIdempotentElemEquivClopens.symm U
  rw [eq_sub_iff_add_eq', SplitK0.one_def]
  refine (SplitK0.of_eq_add_of_linearEquiv_prod ?_).symm
  exact (AlgEquiv.prodQuotientOfIsIdempotentElem R e.prop.one_sub e.prop (sub_add_cancel 1 e.val)
    e.prop.one_sub_mul_self).toLinearEquiv.trans ((LinearEquiv.refl R _).prodCongr
      (Submodule.quotEquivOfEq _ _ (by simp [e])))

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

end FiniteProjectiveModules

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Quotient
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Free actions of finite locally free group schemes are torsors over their invariants

Let `H` be a commutative Hopf algebra over `R` and `A` a commutative `H`-comodule algebra, so
that the affine group scheme `G = Spec H` acts on `X = Spec A` by `X × G ⟶ X`. The action is
**free** when `X × G ⟶ X × X`, `(x, g) ↦ (x, x g)`, is a closed immersion, that is, when the
Galois map over the base ring `A ⊗[R] A → A ⊗[R] H`, `a ⊗ a' ↦ (a ⊗ 1) coact(a')`, is surjective.

This file proves the Hopf–Galois criterion for a finite locally free `G`: if `H` is a finite
projective `R`-module, the action is free if and only if `A` is faithfully flat over the
coinvariants `A^{co H}` and the Galois map `A ⊗[A^{co H}] A → A ⊗[R] H` is bijective
(`TauCeti.ComoduleAlgebra.surjective_galoisMap_iff`); the converse direction holds for any
torsor (`TauCeti.ComoduleAlgebra.surjective_galoisMap_of_surjective_galoisMap`). So for a free
action `X ⟶ Spec A^{co H}` is a `G`-torsor, and the results on Hopf–Galois extensions apply to
it: `Spec A^{co H}` is the categorical quotient of `X` by `G` in schemes
(`TauCeti.ComoduleAlgebra.existsUnique_SpecMap_comp_eq`), the projection is finite
(`TauCeti.ComoduleAlgebra.finite_of_bijective_galoisMap`), and it represents the fppf quotient
sheaf (`TauCeti.ComoduleAlgebra.existsUnique_fppfYoneda_comp_eq_of_bijective_galoisMap`).

The proof reduces to the quotient of an affine scheme by a finite locally free equivalence
relation (SGA 3, Exposé V, Théorème 4.1). The two maps `s, t : A → A ⊗[R] H`, `a ↦ a ⊗ 1` and the
coaction, are the projection and the action `X × G ⇉ X`. They form an equivalence relation
(`TauCeti.ComoduleAlgebra.isSpecEquivRel_of_surjective_galoisMap`): on `T`-points the pair
`(x, g)` relates `x` to `x g`, reflexivity is the unit of `G`, symmetry sends `(x, g)` to
`(x g, g⁻¹)` using the antipode, transitivity sends `(x, g)` and `(x g, g')` to `(x, g g')`
using the comultiplication, and freeness says that `(x, g)` is determined by `(x, x g)`. The
ring of invariants `{a : s a = t a}` of this relation is `A^{co H}`
(`TauCeti.ComoduleAlgebra.eqLocus_coactAlgHom`), and `A ⊗[R] H` is finite projective over `A`
through `s` because `H` is finite projective over `R`. So `A` is faithfully flat over `A^{co H}`
(`RingHom.IsSpecEquivRel.faithfullyFlat`) and the relation is the kernel pair of
`X ⟶ Spec A^{co H}` (`RingHom.IsSpecEquivRel.isPushout`), which is bijectivity of the Galois map.

## Main results

* `TauCeti.ComoduleAlgebra.isSpecEquivRel_of_surjective_galoisMap`: a free action is an
  equivalence relation.
* `TauCeti.ComoduleAlgebra.faithfullyFlat_coinvariants_of_surjective_galoisMap` and
  `TauCeti.ComoduleAlgebra.bijective_galoisMap_coinvariants_of_surjective_galoisMap`: a free action
  of a finite locally free group scheme is a torsor over the coinvariants.
* `TauCeti.ComoduleAlgebra.surjective_galoisMap_iff`: the Hopf–Galois criterion.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, Théorème 4.1 and
  Exposé IV, §5.
* H. F. Kreimer and M. Takeuchi, *Hopf algebras and Galois extensions of an algebra*, Indiana Univ.
  Math. J. **30** (1981), 675–692.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §8.1.
-/

public section

open CategoryTheory Limits TensorProduct Algebra.TensorProduct

namespace TauCeti.ComoduleAlgebra

universe u

section Hopf

variable {R : Type*} {H A : Type u} [CommSemiring R] [CommRing H] [HopfAlgebra R H] [CommRing A]
  [Algebra R A] [ComoduleAlgebra R H A]

/-! ### The action groupoid

A point `x : A ⊗[R] H →+* T` of `Spec A × Spec H` is a pair `(u, g)`, with `u = x ∘ s` and `g` the
restriction of `x` to `H`, and it relates `u` to `x ∘ t = u g`. -/

variable {T : Type u} [CommRing T]

-- `(a ⊗ h) ⊗ h' ↦ x (a ⊗ h) τ(h')`, on `a ⊗ v` for `v : H ⊗[R] H`
omit [ComoduleAlgebra R H A] in
private theorem liftRingHom_assoc_symm_tmul (x : A ⊗[R] H →+* T) (τ : H →+* T)
    (hτ : x.comp (algebraMap R (A ⊗[R] H)) = τ.comp (algebraMap R H))
    (hτ' : (x.comp (includeRight : H →ₐ[R] A ⊗[R] H).toRingHom).comp (algebraMap R H) =
      τ.comp (algebraMap R H)) (a : A) (v : H ⊗[R] H) :
    liftRingHom x τ hτ ((TensorProduct.assoc R A H H).symm (a ⊗ₜ v)) =
      x (a ⊗ₜ 1) * liftRingHom (x.comp (includeRight : H →ₐ[R] A ⊗[R] H).toRingHom) τ hτ' v := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp [mul_add, tmul_add, hv, hv']
  | tmul h₁ h₂ => simp [← mul_assoc, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

-- `(coact a) ⊗ h ↦ x (coact a) τ(h)`
private theorem liftRingHom_rTensor_coact (x : A ⊗[R] H →+* T) (τ : H →+* T)
    (hτ : x.comp (algebraMap R (A ⊗[R] H)) = τ.comp (algebraMap R H))
    (hτ' : (x.comp (coactAlgHom R H A).toRingHom).comp (algebraMap R A) =
      τ.comp (algebraMap R H)) (w : A ⊗[R] H) :
    liftRingHom x τ hτ ((Comodule.coact (R := R) (C := H) (M := A)).rTensor H w) =
      liftRingHom (x.comp (coactAlgHom R H A).toRingHom) τ hτ' w := by
  induction w using TensorProduct.inductionOn with
  | tmul a h => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']

-- reflexivity: the point `(u, 1)` relates `u` to itself
private theorem exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq (u : A →+* T) :
    ∃ z : A ⊗[R] H →+* T, z.comp (algebraMap A (A ⊗[R] H)) = u ∧
      z.comp (coactAlgHom R H A).toRingHom = u := by
  -- `a ⊗ h ↦ ε(h) a`
  let ε : A ⊗[R] H →ₐ[R] A :=
    lift (AlgHom.id R A) ((Algebra.ofId R A).comp (Bialgebra.counitAlgHom R H))
      fun _ _ ↦ .all _ _
  have hε (w : A ⊗[R] H) : ε w = TensorProduct.rid R A (Coalgebra.counit.lTensor A w) := by
    induction w using TensorProduct.inductionOn with
    | tmul a h => simp [ε, Algebra.smul_def, mul_comm]
    | add w w' hw hw' => simp [hw, hw']
  refine ⟨u.comp ε.toRingHom, ?_, ?_⟩
  · ext a
    simp [ε]
  · ext a
    simp [hε]

-- symmetry: the point `(u g, g⁻¹)` relates `u g` to `u`
private theorem exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq_symm (x : A ⊗[R] H →+* T) :
    ∃ z : A ⊗[R] H →+* T, z.comp (algebraMap A (A ⊗[R] H)) = x.comp (coactAlgHom R H A).toRingHom ∧
      z.comp (coactAlgHom R H A).toRingHom = x.comp (algebraMap A (A ⊗[R] H)) := by
  let ι : H →+* A ⊗[R] H := (includeRight : H →ₐ[R] A ⊗[R] H).toRingHom
  -- `g⁻¹ = g ∘ S`
  let σ : H →+* T := (x.comp ι).comp (HopfAlgebra.antipodeAlgHom R H).toRingHom
  have hσ : (x.comp (coactAlgHom R H A).toRingHom).comp (algebraMap R A) =
      σ.comp (algebraMap R H) := by
    ext r
    simp [σ, ι]
  have hσR : x.comp (algebraMap R (A ⊗[R] H)) = σ.comp (algebraMap R H) := by
    ext r
    simp [σ, ι]
  have hσι : (x.comp ι).comp (algebraMap R H) = σ.comp (algebraMap R H) := by
    ext r
    simp [σ, ι]
  -- `(a ⊗ h) ⊗ h' ↦ x (a ⊗ h) g⁻¹(h')`
  let Ψ : (A ⊗[R] H) ⊗[R] H →+* T := liftRingHom x σ hσR
  -- `∑ g(h₁) g⁻¹(h₂) = g (S h₁ h₂)`
  have hgσ (v : H ⊗[R] H) :
      liftRingHom (x.comp ι) σ hσι v =
        x (1 ⊗ₜ LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H v)) := by
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp [tmul_add, hv, hv']
    | tmul h₁ h₂ => simp [σ, ι, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
  -- `∑ x (a ⊗ h₁) g⁻¹(h₂) = x (a ⊗ ε(h))`
  have hΨ (w : A ⊗[R] H) :
      Ψ ((TensorProduct.assoc R A H H).symm (Coalgebra.comul.lTensor A w)) =
        x (algebraMap A _ (TensorProduct.rid R A (Coalgebra.counit.lTensor A w))) := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul a h =>
      rw [LinearMap.lTensor_tmul, liftRingHom_assoc_symm_tmul x σ hσR hσι, hgσ,
        HopfAlgebra.mul_antipode_lTensor_comul_apply]
      simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := H), TensorProduct.smul_tmul']
  refine ⟨liftRingHom (x.comp (coactAlgHom R H A).toRingHom) σ hσ, ?_, ?_⟩
  · ext a
    simp [σ]
  · ext a
    have := hΨ (Comodule.coact a)
    rw [← Comodule.coassoc_apply, LinearEquiv.symm_apply_apply,
      liftRingHom_rTensor_coact x σ hσR hσ, Comodule.lTensor_counit_coact] at this
    simpa using this

-- transitivity: the points `(u, g)` and `(u g, g')` give the point `(u, g g')`
private theorem exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq_trans (x y : A ⊗[R] H →+* T)
    (hxy : x.comp (coactAlgHom R H A).toRingHom = y.comp (algebraMap A (A ⊗[R] H))) :
    ∃ z : A ⊗[R] H →+* T, z.comp (algebraMap A (A ⊗[R] H)) = x.comp (algebraMap A (A ⊗[R] H)) ∧
      z.comp (coactAlgHom R H A).toRingHom = y.comp (coactAlgHom R H A).toRingHom := by
  let ι : H →+* A ⊗[R] H := (includeRight : H →ₐ[R] A ⊗[R] H).toRingHom
  -- `g` and `g'` agree on `R`
  have hR : (x.comp ι).comp (algebraMap R H) = (y.comp ι).comp (algebraMap R H) := by
    ext r
    have := congr($hxy (algebraMap R A r))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply] at this
    simpa only [RingHom.comp_apply, ι, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes] using this
  have hRx : x.comp (algebraMap R (A ⊗[R] H)) = (y.comp ι).comp (algebraMap R H) := by
    ext r
    simpa [ι, ← IsScalarTower.algebraMap_apply] using congr($hR r)
  -- `g g' = (g ⊗ g') ∘ Δ`
  let γ : H →+* T :=
    (liftRingHom (x.comp ι) (y.comp ι) hR).comp (Bialgebra.comulAlgHom R H).toRingHom
  have hγ : (x.comp (algebraMap A (A ⊗[R] H))).comp (algebraMap R A) =
      γ.comp (algebraMap R H) := by
    ext r
    simp [γ, ι, ← Algebra.TensorProduct.one_def]
  -- `(a ⊗ h) ⊗ h' ↦ x (a ⊗ h) g'(h')`
  let Ψ : (A ⊗[R] H) ⊗[R] H →+* T := liftRingHom x (y.comp ι) hRx
  let z := liftRingHom (x.comp (algebraMap A (A ⊗[R] H))) γ hγ
  -- `z (a ⊗ h) = ∑ x (a ⊗ h₁) g'(h₂)`
  have hz (w : A ⊗[R] H) :
      z w = Ψ ((TensorProduct.assoc R A H H).symm (Coalgebra.comul.lTensor A w)) := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul a h =>
      rw [LinearMap.lTensor_tmul, liftRingHom_assoc_symm_tmul x (y.comp ι) hRx hR]
      simp [z, γ, ι]
  -- `Ψ ((coact a) ⊗ h) = x (coact a) g'(h) = y (a ⊗ h)`
  have hΨ (w : A ⊗[R] H) :
      Ψ ((Comodule.coact (R := R) (C := H) (M := A)).rTensor H w) = y w := by
    rw [liftRingHom_rTensor_coact x (y.comp ι) hRx (by rw [hxy]; ext r; simp [ι])]
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul a h =>
      have : x (Comodule.coact a) = y (a ⊗ₜ 1) := by simpa using congr($hxy a)
      simp [ι, this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
  refine ⟨z, ?_, ?_⟩
  · ext a
    simp [z]
  · ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coactAlgHom_apply]
    rw [hz, ← Comodule.coassoc_apply, LinearEquiv.symm_apply_apply, hΨ]

/-- **A free action is an equivalence relation.** If the Galois map `A ⊗[R] A → A ⊗[R] H` is
surjective, then the projection and the action `Spec (A ⊗[R] H) ⇉ Spec A`, given by `a ↦ a ⊗ 1`
and the coaction, form an equivalence relation. -/
theorem isSpecEquivRel_of_surjective_galoisMap
    (hfree : Function.Surjective (galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r)) :
    (algebraMap A (A ⊗[R] H)).IsSpecEquivRel (coactAlgHom R H A).toRingHom := by
  refine ⟨fun T _ x y hs ht ↦ ?_, fun _ _ ↦ exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq,
    fun _ _ ↦ exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq_symm,
    fun _ _ ↦ exists_comp_algebraMap_eq_and_comp_coactAlgHom_eq_trans⟩
  -- freeness: `A ⊗[R] H` is spanned by the products of the images of `s` and `t`
  refine RingHom.ext fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hfree w
  induction v using TensorProduct.inductionOn with
  | tmul a a' =>
    have h₁ : x (a ⊗ₜ 1) = y (a ⊗ₜ 1) := by simpa using congr($hs a)
    have h₂ : x (Comodule.coact a') = y (Comodule.coact a') := by simpa using congr($ht a')
    simp [h₁, h₂]
  | add v v' hv hv' => simp [hv, hv']

end Hopf

section Ring

variable {R : Type*} {H A : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing A]
  [Algebra R A] [ComoduleAlgebra R H A]

-- the invariants of the relation, identified with the coinvariants
private noncomputable def eqLocusEquiv :
    (algebraMap A (A ⊗[R] H)).eqLocus (coactAlgHom R H A).toRingHom ≃+* coinvariants R H A :=
  RingEquiv.subsemiringCongr (SetLike.coe_injective eqLocus_coactAlgHom)

variable [Module.Finite R H] [Module.Projective R H]

/-- **A free action is a torsor over the coinvariants: faithful flatness.** Let `H` be a
commutative Hopf algebra which is a finite projective `R`-module and `A` a commutative
`H`-comodule algebra on which the action is free, in the sense that the Galois map
`A ⊗[R] A → A ⊗[R] H` is surjective. Then `A` is faithfully flat over its coinvariants. -/
theorem faithfullyFlat_coinvariants_of_surjective_galoisMap
    (hfree : Function.Surjective (galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r)) :
    Module.FaithfullyFlat (coinvariants R H A) A := by
  have := (isSpecEquivRel_of_surjective_galoisMap hfree).faithfullyFlat
  rw [← RingHom.faithfullyFlat_algebraMap_iff] at this ⊢
  exact RingHom.FaithfullyFlat.respectsIso.2 _ eqLocusEquiv.symm this

/-- **A free action is a torsor over the coinvariants: the Galois isomorphism.** Let `H` be a
commutative Hopf algebra which is a finite projective `R`-module and `A` a commutative
`H`-comodule algebra on which the action is free, in the sense that the Galois map
`A ⊗[R] A → A ⊗[R] H` is surjective. Then the Galois map `A ⊗[A^{co H}] A → A ⊗[R] H` over the
coinvariants is bijective: `Spec A × Spec H ≅ Spec A ×_{Spec A^{co H}} Spec A`. -/
theorem bijective_galoisMap_coinvariants_of_surjective_galoisMap
    (hfree : Function.Surjective (galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r)) :
    Function.Bijective (galoisMap (coinvariants R H A) algebraMap_coinvariants_mem) := by
  -- the relation is the pushout of `A^{co H} → A` along itself, as is `A ⊗[A^{co H}] A`;
  -- `eqLocusEquiv` is the identity on underlying elements of `A`, so the corner commutes by `rfl`
  have hP := ((isSpecEquivRel_of_surjective_galoisMap hfree).isPushout).of_iso
    (f' := CommRingCat.ofHom (algebraMap (coinvariants R H A) A))
    (g' := CommRingCat.ofHom (algebraMap (coinvariants R H A) A))
    (inl' := CommRingCat.ofHom (algebraMap A (A ⊗[R] H)))
    (inr' := CommRingCat.ofHom (coactAlgHom R H A).toRingHom)
    (RingEquiv.toCommRingCatIso eqLocusEquiv) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by ext; rfl) (by ext; rfl) (by simp) (by simp)
  have hT := CommRingCat.isPushout_tensorProduct (coinvariants R H A) A A
  -- the comparison isomorphism of the two pushouts is the Galois map
  have : CommRingCat.ofHom (galoisMap (coinvariants R H A) algebraMap_coinvariants_mem).toRingHom =
      (hT.isoIsPushout _ _ hP).hom := by
    refine hT.hom_ext ?_ ?_
    · rw [IsPushout.inl_isoIsPushout_hom]
      ext a
      simp
    · rw [IsPushout.inr_isoIsPushout_hom]
      ext a
      simp [← Algebra.TensorProduct.one_def]
  have hbij := ConcreteCategory.bijective_of_isIso (hT.isoIsPushout _ _ hP).hom
  rw [← this] at hbij
  exact hbij

/-- **The Hopf–Galois criterion.** Let `H` be a commutative Hopf algebra which is a finite
projective `R`-module, so that `G = Spec H` is a finite locally free group scheme over `Spec R`,
and let `A` be a commutative `H`-comodule algebra. The action of `G` on `Spec A` is free, in the
sense that the Galois map `A ⊗[R] A → A ⊗[R] H` is surjective, if and only if `A` is faithfully
flat over its coinvariants `A^{co H}` and the Galois map `A ⊗[A^{co H}] A → A ⊗[R] H` is
bijective, that is, `Spec A ⟶ Spec A^{co H}` is a `G`-torsor. -/
theorem surjective_galoisMap_iff :
    Function.Surjective (galoisMap R fun r ↦ (coinvariants R H A).algebraMap_mem r) ↔
      Module.FaithfullyFlat (coinvariants R H A) A ∧
        Function.Bijective (galoisMap (coinvariants R H A) algebraMap_coinvariants_mem) :=
  ⟨fun h ↦ ⟨faithfullyFlat_coinvariants_of_surjective_galoisMap h,
    bijective_galoisMap_coinvariants_of_surjective_galoisMap h⟩,
    fun h ↦ surjective_galoisMap_of_surjective_galoisMap _ h.2.2⟩

end Ring

end TauCeti.ComoduleAlgebra

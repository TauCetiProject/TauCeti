/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.ScalarChange
public import TauCeti.RingTheory.Idempotents.Clopen.RankModule

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
import TauCeti.Order.Disjoint
import TauCeti.RingTheory.Flat.Semilocal
import TauCeti.RingTheory.Idempotents.Connected.Rank
import TauCeti.RingTheory.Idempotents.Module
import TauCeti.RingTheory.Idempotents.Projective
import TauCeti.RingTheory.Idempotents.TensorProduct
import TauCeti.Topology.LocallyConstant.Connected

/-!
# The locally constant rank homomorphism on `K₀`, reduced `K₀`, and semilocal / PID classification

For a commutative ring `R`, the split Grothendieck group
`SplitK0.{u} (finiteProjectiveModules R).FullSubcategory` is a commutative ring under the tensor
product (`TauCeti.SplitK0.instCommRing`). Every finitely generated projective `R`-module `P` is
finitely presented and flat, so its stalk rank `p ↦ Module.rankAtStalk P p` is locally constant on
`Spec R`, additive on direct sums, sends `R` to `1`, and is multiplicative on tensor products.
By the universal property `TauCeti.SplitK0.liftRingHom`, stalk rank therefore descends to a
natural ring homomorphism

```text
rankHom R : K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ.
```

Using the correspondence between clopen subsets `U ⊆ Spec R` and idempotents `e_U ∈ R`, each
clopen `U` defines a finitely generated projective module `R e_U` whose class `clopenClass R U`
has rank equal to the characteristic function `LocallyConstant.charFn ℤ U.isClopen`. Extending
additively over the finite clopen fibers of any `g : LocallyConstant (PrimeSpectrum R) ℤ` yields
a natural ring-homomorphism section `rankSection R` with `(rankHom R).comp (rankSection R) = id`.
Thus `K₀(proj R)` splits additively as `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`, where
`reducedK0 R := RingHom.ker (rankHom R)` is the reduced `K₀` ideal.

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankHom`: the locally constant rank ring homomorphism
  `K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ`.
* `TauCeti.FiniteProjectiveModules.clopenObj`, `clopenClass`, and `clopenRankObj`: the
  finitely generated projective modules and `K₀` classes attached to clopen subsets of `Spec R`
  and locally constant `ℕ`-valued rank functions.
* `TauCeti.FiniteProjectiveModules.rankSection`: the natural ring-homomorphism section
  `LocallyConstant (PrimeSpectrum R) ℤ →+* K₀(proj R)` of `rankHom R`.
* `TauCeti.FiniteProjectiveModules.reducedK0`: the ideal `RingHom.ker (rankHom R)` of rank-zero
  classes, together with the splitting `splitK0EquivProdReducedK0`.
* `TauCeti.FiniteProjectiveModules.rankEquivOfFiniteMaximalSpectrum`: for a commutative semilocal
  ring (`Finite (MaximalSpectrum R)`), the ring isomorphism
  `K₀(proj R) ≃+* LocallyConstant (PrimeSpectrum R) ℤ`.
* `TauCeti.FiniteProjectiveModules.rankEquivIntOfForallFree`,
  `rankEquivIntOfFiniteMaximalSpectrum`, and `rankEquivIntOfIsPrincipalIdealRing`: the ring
  isomorphism `K₀(proj R) ≃+* ℤ` whenever every finite projective `R`-module is free (over a
  nontrivial commutative ring) — in particular for connected semilocal rings (including all
  commutative local rings) and principal ideal domains.

## Main results

* `TauCeti.FiniteProjectiveModules.rankHom_comp_extend` and `extend_comp_rankSection`: naturality
  of `rankHom` and `rankSection` under ring homomorphisms.
* `TauCeti.FiniteProjectiveModules.rankHom_comp_rankSection`: `rankSection R` is a right inverse
  to `rankHom R`, so `rankHom R` is surjective and `rankSection R` is injective.
* `TauCeti.FiniteProjectiveModules.mem_reducedK0_iff_forall_localization`: a class in `K₀(proj R)`
  lies in `reducedK0 R` if and only if its image vanishes in `K₀(proj R_p)` at every prime `p`.
* `TauCeti.FiniteProjectiveModules.rankSection_comp_rankHom_eq_id_of_forall_clopenRankModule` and
  `reducedK0_eq_bot_of_rankSection_comp_rankHom`: general classification criterion via clopen-glued
  models and its kernel-vanishing consequence.
* `TauCeti.FiniteProjectiveModules.reducedK0_eq_bot_of_finite_maximalSpectrum` and
  `reducedK0_eq_bot_of_forall_free`: vanishing of reduced `K₀` for semilocal rings and rings whose
  finitely generated projective modules are free.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Lemmas 2.2–2.3 and Corollary 2.6.2, pp. 71–75.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §§1.1–1.3.
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti.FiniteProjectiveModules

section RankHom

variable {R : Type u} [CommRing R]

/-- The underlying module of an object of the subcategory of finitely generated projectives over
a commutative ring is finitely presented. -/
instance (P : (finiteProjectiveModules R).FullSubcategory) :
    Module.FinitePresentation R P.obj :=
  Module.finitePresentation_of_projective R P.obj

/-- The underlying module of an object of the subcategory of finitely generated projectives over
a commutative ring is flat. -/
instance (P : (finiteProjectiveModules R).FullSubcategory) :
    Module.Flat R P.obj :=
  Module.Flat.of_projective

variable (R)

/-- Stalk rank as a biproduct-additive invariant taking values in
`LocallyConstant (PrimeSpectrum R) ℤ`. -/
private noncomputable def rankInvariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory
      (LocallyConstant (PrimeSpectrum R) ℤ) where
  obj P := (Module.rankLocallyConstant R P.obj).map (Nat.cast : ℕ → ℤ)
  map_iso {P Q} e := by
    ext p
    simp only [LocallyConstant.map_apply, Function.comp_apply, Module.rankLocallyConstant_apply,
      Nat.cast_inj]
    exact congrFun (Module.rankAtStalk_eq_of_equiv
      ((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv) p
  map_biprod P Q := by
    ext p
    simp [congrFun (Module.rankAtStalk_eq_of_equiv (biprodLinearEquiv P Q)) p,
      congrFun (Module.rankAtStalk_prod (R := R) P.obj Q.obj) p]

private theorem rankInvariant_apply (P : (finiteProjectiveModules R).FullSubcategory)
    (p : PrimeSpectrum R) :
    (rankInvariant R).obj P p = (Module.rankAtStalk (R := R) P.obj p : ℤ) := by
  simp [rankInvariant]

/-- **The locally constant rank homomorphism.** Stalk rank on finitely generated projective
`R`-modules descends to a ring homomorphism
`K₀(proj R) →+* LocallyConstant (PrimeSpectrum R) ℤ`. -/
noncomputable def rankHom :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  SplitK0.liftRingHom (rankInvariant R)
    (by
      ext p
      have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩
      rw [LocallyConstant.one_apply, rankInvariant_apply,
        congrFun (Module.rankAtStalk_eq_of_equiv (eqToIso (tensorUnit_obj R)).toLinearEquiv) p,
        congrFun (Module.rankAtStalk_self (R := R)) p, Pi.one_apply, Nat.cast_one])
    (fun P Q ↦ by
      ext p
      rw [LocallyConstant.mul_apply, rankInvariant_apply, rankInvariant_apply, rankInvariant_apply,
        congrFun (Module.rankAtStalk_eq_of_equiv (eqToIso (tensorObj_obj P Q)).toLinearEquiv) p,
        congrFun (Module.rankAtStalk_tensorProduct (R := R) (M := P.obj) Q.obj) p,
        Pi.mul_apply, Nat.cast_mul])

@[simp]
theorem rankHom_of (P : (finiteProjectiveModules R).FullSubcategory) :
    rankHom R (SplitK0.of.{u} P) =
      (Module.rankLocallyConstant R P.obj).map (Nat.cast : ℕ → ℤ) := by
  rw [rankHom, SplitK0.liftRingHom_of, rankInvariant]

theorem rankHom_of_apply (P : (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankHom R (SplitK0.of.{u} P) p = (Module.rankAtStalk (R := R) P.obj p : ℤ) := by
  simp

theorem rankHom_of_free (P : (finiteProjectiveModules R).FullSubcategory) [Module.Free R P.obj] :
    rankHom R (SplitK0.of.{u} P) =
      LocallyConstant.const (PrimeSpectrum R) (Module.finrank R P.obj : ℤ) := by
  ext p
  simp [congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P.obj)) p]

/-- **Naturality of rank under scalar extension.** For `f : R →+* S`, rank commutes with scalar
extension along `f` and pullback of locally constant functions along `Spec S → Spec R`. -/
theorem rankHom_comp_extend {S : Type u} [CommRing S] (f : R →+* S) :
    (rankHom S).comp f.finiteProjectiveModulesSplitK0Extend =
      (LocallyConstant.comapRingHom ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).comp
        (rankHom R) := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  ext q
  let : Algebra R S := f.toAlgebra
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.finiteProjectiveModulesSplitK0Extend_of,
    rankHom_of_apply]
  have h := (congrFun (Module.rankAtStalk_eq_of_equiv
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P)).toLinearEquiv) q).trans
    ((congrFun (Module.rankAtStalk_eq_of_equiv
      (BalancedExtension.equivTensorProduct R S P.obj)) q).trans
      (Module.rankAtStalk_baseChange (R := R) (S := S) (M := P.obj) q))
  exact (congrArg (Nat.cast : ℕ → ℤ) h).trans (rankHom_of_apply R P (q.comap f)).symm

@[simp]
theorem rankHom_extend_apply {S : Type u} [CommRing S] (f : R →+* S)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (q : PrimeSpectrum S) :
    rankHom S (f.finiteProjectiveModulesSplitK0Extend x) q = rankHom R x (q.comap f) :=
  DFunLike.congr_fun (DFunLike.congr_fun (rankHom_comp_extend R f) x) q

end RankHom

/-! ### Clopen idempotent classes and the rank section -/

section RankSection

open PrimeSpectrum (isIdempotentElemEquivClopens)

variable (R : Type u) [CommRing R]

/-- The finitely generated projective `R`-module `R e_U` attached to a clopen subset
`U ⊆ Spec R`. -/
noncomputable def clopenObj (U : Clopens (PrimeSpectrum R)) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Ideal.span {(isIdempotentElemEquivClopens.symm U).val} : Ideal R),
    finiteProjectiveModules_iff.2 ⟨Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _),
      (isIdempotentElemEquivClopens.symm U).property.projective_span_singleton⟩⟩

/-- `clopenObj R U` has underlying module
`Ideal.span {(isIdempotentElemEquivClopens.symm U).val}`. -/
@[simp]
theorem clopenObj_obj (U : Clopens (PrimeSpectrum R)) :
    (clopenObj R U).obj =
      ModuleCat.of R (Ideal.span {(isIdempotentElemEquivClopens.symm U).val} : Ideal R) :=
  (rfl)

/-- The class `[R e_U]` in `K₀(proj R)` attached to a clopen subset `U ⊆ Spec R`. -/
noncomputable def clopenClass (U : Clopens (PrimeSpectrum R)) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  SplitK0.of.{u} (clopenObj R U)

/-- `ClopenRankModule R f` as an object of `(finiteProjectiveModules R).FullSubcategory`. -/
noncomputable def clopenRankObj (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (ClopenRankModule R f),
    finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

/-- `(clopenRankObj R f).obj` is `ModuleCat.of R (ClopenRankModule R f)`. -/
@[simp]
theorem clopenRankObj_obj (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    (clopenRankObj R f).obj = ModuleCat.of R (ClopenRankModule R f) :=
  (rfl)

@[simp]
theorem clopenClass_bot : clopenClass R ⊥ = 0 := by
  have : Subsingleton ((finiteProjectiveModules R).ι.obj (clopenObj R ⊥)) := by
    dsimp only [clopenObj, ObjectProperty.ι_obj]
    rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot, Ideal.span_singleton_zero]
    infer_instance
  exact SplitK0.of_eq_zero_of_isZero (Limits.IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules R).ι (clopenObj R ⊥) (ModuleCat.isZero_of_subsingleton _))

@[simp]
theorem clopenClass_top : clopenClass R ⊤ = 1 := by
  rw [clopenClass, SplitK0.one_def]
  exact SplitK0.of_congr (ObjectProperty.isoMk _
    ((LinearEquiv.ofEq _ _ (by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top, Ideal.span_singleton_one])).trans
      Submodule.topEquiv).toModuleIso)

theorem clopenClass_inf (U V : Clopens (PrimeSpectrum R)) :
    clopenClass R (U ⊓ V) = clopenClass R U * clopenClass R V := by
  rw [clopenClass, clopenClass, clopenClass, SplitK0.of_mul_of]
  exact SplitK0.of_congr (ObjectProperty.isoMk _
    ((LinearEquiv.ofEq _ _ (by
      rw [congrArg Subtype.val (PrimeSpectrum.isIdempotentElemEquivClopens_symm_inf U V)])).trans
      ((isIdempotentElemEquivClopens.symm U).property.spanSingletonTensorEquiv
        (isIdempotentElemEquivClopens.symm V).property).symm).toModuleIso)

theorem clopenClass_sup_of_disjoint {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    clopenClass R (U ⊔ V) = clopenClass R U + clopenClass R V :=
  SplitK0.of_eq_add_of_linearEquiv_prod (X := clopenObj R (U ⊔ V))
    (P := clopenObj R U) (Q := clopenObj R V) <|
    (LinearEquiv.ofEq _ _ (by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_sup_of_disjoint h])).trans
      ((isIdempotentElemEquivClopens.symm U).property.spanSingletonAddEquivProd
        (isIdempotentElemEquivClopens.symm V).property
        (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h)
        (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h.symm))

theorem clopenClass_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : (s : Set ι).PairwiseDisjoint U) :
    clopenClass R (s.sup U) = ∑ i ∈ s, clopenClass R (U i) :=
  hdisj.map_finset_sup (clopenClass R) (clopenClass_bot R)
    fun _ _ h ↦ clopenClass_sup_of_disjoint R h

theorem clopenClass_add_compl (U : Clopens (PrimeSpectrum R)) :
    clopenClass R U + clopenClass R Uᶜ = 1 := by
  rw [← clopenClass_sup_of_disjoint R disjoint_compl_right, sup_compl_eq_top, clopenClass_top]

@[simp]
theorem rankHom_clopenClass (U : Clopens (PrimeSpectrum R)) :
    rankHom R (clopenClass R U) = LocallyConstant.charFn ℤ U.isClopen := by
  ext p
  rw [clopenClass, rankHom_of_apply,
    congrFun (Module.rankAtStalk_eq_of_equiv (eqToIso (clopenObj_obj R U)).toLinearEquiv) p,
    (isIdempotentElemEquivClopens.symm U).property.rankAtStalk_span_singleton p,
    PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff]
  by_cases hp : p ∈ U <;> simp [LocallyConstant.coe_charFn, hp]

theorem extend_clopenClass {S : Type u} [CommRing S] (f : R →+* S)
    (U : Clopens (PrimeSpectrum R)) :
    f.finiteProjectiveModulesSplitK0Extend (clopenClass R U) =
      clopenClass S ⟨PrimeSpectrum.comap f ⁻¹' U,
        U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩ := by
  rw [clopenClass, RingHom.finiteProjectiveModulesSplitK0Extend_of, clopenClass]
  exact SplitK0.of_extendScalars_obj
    (Q := clopenObj S ⟨PrimeSpectrum.comap f ⁻¹' U,
      U.isClopen.preimage (PrimeSpectrum.continuous_comap f)⟩) <|
    ((isIdempotentElemEquivClopens.symm U).property.balancedExtensionSpanSingletonEquiv f).trans
      (LinearEquiv.ofEq _ _ (by rw [PrimeSpectrum.map_isIdempotentElemEquivClopens_symm]))

/-- Refining a clopen class along any finite clopen partition of `Spec R`. -/
private theorem clopenClass_eq_sum_inf {κ : Type*} (t : Finset κ)
    (U : Clopens (PrimeSpectrum R)) (V : κ → Clopens (PrimeSpectrum R))
    (hVd : (t : Set κ).PairwiseDisjoint V) (hVc : t.sup V = ⊤) :
    clopenClass R U = ∑ j ∈ t, clopenClass R (U ⊓ V j) := by
  have heq : U = t.sup fun j ↦ U ⊓ V j := Clopens.ext <| by
    have hp : ∀ p, ∃ j ∈ t, p ∈ V j := fun p ↦ by
      have : p ∈ (t.sup V : Clopens (PrimeSpectrum R)) := by rw [hVc]; trivial
      simpa [← SetLike.mem_coe, Clopens.coe_finset_sup] using this
    ext p
    simp only [Clopens.coe_finset_sup, Clopens.coe_inf, Set.mem_iUnion, Set.mem_inter_iff,
      SetLike.mem_coe, exists_prop]
    exact ⟨fun h ↦ let ⟨j, hj, hpj⟩ := hp p; ⟨j, hj, h, hpj⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  conv_lhs => rw [heq]
  exact clopenClass_finset_sup R t _ fun j₁ hj₁ j₂ hj₂ hne ↦
    (hVd hj₁ hj₂ hne).mono inf_le_right inf_le_right

/-- Partition independence for `ℤ`-linear combinations of clopen classes: two finite clopen
partitions with matching weights on every nonempty overlap yield the same class in `K₀(proj R)`. -/
private theorem sum_smul_clopenClass_eq_of_partition {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (U : ι → Clopens (PrimeSpectrum R)) (V : κ → Clopens (PrimeSpectrum R))
    (c : ι → ℤ) (d : κ → ℤ)
    (hUd : (s : Set ι).PairwiseDisjoint U) (hUc : s.sup U = ⊤)
    (hVd : (t : Set κ).PairwiseDisjoint V) (hVc : t.sup V = ⊤)
    (hagree : ∀ i ∈ s, ∀ j ∈ t, U i ⊓ V j ≠ ⊥ → c i = d j) :
    ∑ i ∈ s, c i • clopenClass R (U i) = ∑ j ∈ t, d j • clopenClass R (V j) := by
  calc ∑ i ∈ s, c i • clopenClass R (U i)
      = ∑ i ∈ s, ∑ j ∈ t, c i • clopenClass R (U i ⊓ V j) := Finset.sum_congr rfl fun i _ ↦ by
        rw [clopenClass_eq_sum_inf R t (U i) V hVd hVc, Finset.smul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ t, d j • clopenClass R (U i ⊓ V j) :=
        Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by
          by_cases hne : U i ⊓ V j = ⊥
          · rw [hne, clopenClass_bot, smul_zero, smul_zero]
          · rw [hagree i hi j hj hne]
    _ = ∑ j ∈ t, d j • clopenClass R (V j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [clopenClass_eq_sum_inf R s (V j) U hUd hUc, Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by rw [inf_comm]

/-- The raw function underlying `rankSection`: sum of `n • [R e_{g⁻¹{n}}]` over the finite range
of `g`. -/
private noncomputable def rankSectionFun (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  ∑ n ∈ g.range_finite.toFinset, n • clopenClass R (g.fiberClopens n)

/-- `rankSectionFun R g` agrees with the weighted sum over any finite clopen partition on which `g`
is constant on each piece. -/
private theorem rankSectionFun_eq_sum_of_partition (g : LocallyConstant (PrimeSpectrum R) ℤ)
    {ι : Type*} (s : Finset ι) (U : ι → Clopens (PrimeSpectrum R)) (c : ι → ℤ)
    (hdisj : (s : Set ι).PairwiseDisjoint U) (hcover : s.sup U = ⊤)
    (hval : ∀ i ∈ s, ∀ p ∈ U i, g p = c i) :
    rankSectionFun R g = ∑ i ∈ s, c i • clopenClass R (U i) := by
  refine sum_smul_clopenClass_eq_of_partition R g.range_finite.toFinset s g.fiberClopens U id c
    (g.pairwise_disjoint_fiberClopens.set_pairwise _) g.finset_sup_fiberClopens hdisj hcover
    fun n _ i hi hne ↦ ?_
  have ⟨p, hpn, hpi⟩ : (↑(g.fiberClopens n ⊓ U i) : Set (PrimeSpectrum R)).Nonempty :=
    Set.ne_empty_iff_nonempty.1 fun h ↦ hne (Clopens.ext h)
  exact (LocallyConstant.mem_fiberClopens.1 hpn).symm.trans (hval i hi p hpi)

private theorem rankSectionFun_eq_sum_joint_fiber
    (g h k : LocallyConstant (PrimeSpectrum R) ℤ) (op : ℤ → ℤ → ℤ)
    (hop : ∀ p, k p = op (g p) (h p)) :
    rankSectionFun R k =
      ∑ ab ∈ g.range_finite.toFinset ×ˢ h.range_finite.toFinset,
        op ab.1 ab.2 • clopenClass R (g.fiberClopens ab.1 ⊓ h.fiberClopens ab.2) :=
  rankSectionFun_eq_sum_of_partition R k _ _ _
    ((g.pairwise_disjoint_fiberClopens_inf h).set_pairwise _)
    (g.finset_sup_fiberClopens_inf h)
    fun _ _ p hp ↦ by
      rw [hop p, LocallyConstant.mem_fiberClopens.1 hp.1, LocallyConstant.mem_fiberClopens.1 hp.2]

private theorem rankSectionFun_add (g h : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSectionFun R (g + h) = rankSectionFun R g + rankSectionFun R h := by
  rw [rankSectionFun_eq_sum_joint_fiber R g h (g + h) (· + ·) (fun _ ↦ rfl),
    rankSectionFun_eq_sum_joint_fiber R g h g (fun a _ ↦ a) (fun _ ↦ rfl),
    rankSectionFun_eq_sum_joint_fiber R g h h (fun _ b ↦ b) (fun _ ↦ rfl)]
  simp_rw [add_zsmul]; exact Finset.sum_add_distrib

private theorem rankSectionFun_mul (g h : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSectionFun R (g * h) = rankSectionFun R g * rankSectionFun R h := by
  rw [rankSectionFun_eq_sum_joint_fiber R g h (g * h) (· * ·) (fun _ ↦ rfl)]
  simp only [rankSectionFun, Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [clopenClass_inf, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **The clopen rank section.** Sending a locally constant function `g : Spec R → ℤ` to the
weighted sum of its clopen-fiber classes defines a ring-homomorphism section of `rankHom R`. -/
noncomputable def rankSection :
    LocallyConstant (PrimeSpectrum R) ℤ →+*
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory where
  toFun := rankSectionFun R
  map_zero' := by
    rw [rankSectionFun_eq_sum_of_partition R 0 ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ 0)
      (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]; simp
  map_one' := by
    rw [rankSectionFun_eq_sum_of_partition R 1 ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ 1)
      (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]; simp
  map_add' := rankSectionFun_add R
  map_mul' := rankSectionFun_mul R

/-- Explicit fiber-sum formula for `rankSection R g`. -/
theorem rankSection_apply (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankSection R g = ∑ n ∈ g.range_finite.toFinset, n • clopenClass R (g.fiberClopens n) :=
  (rfl)

/-- `rankSection R g` is computed by any finite clopen partition of `Spec R` on which `g` is
constant on each piece. -/
theorem rankSection_eq_sum_of_partition (g : LocallyConstant (PrimeSpectrum R) ℤ)
    {ι : Type*} (s : Finset ι) (U : ι → Clopens (PrimeSpectrum R)) (c : ι → ℤ)
    (hdisj : (s : Set ι).PairwiseDisjoint U) (hcover : s.sup U = ⊤)
    (hval : ∀ i ∈ s, ∀ p ∈ U i, g p = c i) :
    rankSection R g = ∑ i ∈ s, c i • clopenClass R (U i) :=
  rankSectionFun_eq_sum_of_partition R g s U c hdisj hcover hval

@[simp]
theorem rankSection_charFn (U : Clopens (PrimeSpectrum R)) :
    rankSection R (LocallyConstant.charFn ℤ U.isClopen) = clopenClass R U := by
  let V : Bool → Clopens (PrimeSpectrum R) := fun b ↦ if b then U else Uᶜ
  let c : Bool → ℤ := fun b ↦ if b then 1 else 0
  have hdisj : ((Finset.univ : Finset Bool) : Set Bool).PairwiseDisjoint V := fun a _ b _ hab ↦ by
    cases a <;> cases b <;>
      simp [Function.onFun, V, disjoint_compl_left, disjoint_compl_right] at hab ⊢
  rw [rankSection_eq_sum_of_partition R _ Finset.univ V c hdisj (by simp [V, sup_compl_eq_top])
    fun b _ p hp ↦ by
      cases b
      · simp only [c, Bool.false_eq_true, ↓reduceIte, LocallyConstant.coe_charFn]
        exact Set.indicator_of_notMem hp 1
      · simp [V] at hp; simp [c, LocallyConstant.coe_charFn, hp]]
  simp [V, c]

@[simp]
theorem rankSection_const (n : ℤ) :
    rankSection R (LocallyConstant.const (PrimeSpectrum R) n) = n := by
  rw [rankSection_eq_sum_of_partition R _ ({()} : Finset Unit) (fun _ ↦ ⊤) (fun _ ↦ n)
    (by simp) (by simp) (fun _ _ _ _ ↦ rfl)]; simp

/-- The finite-projective object `Fin k → R e_{f⁻¹{k}}` for a rank fiber `k`. -/
private noncomputable def clopenRankPiece (f : LocallyConstant (PrimeSpectrum R) ℕ) (k : ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Fin k → (clopenObj R (f.fiberClopens k)).obj),
    finiteProjectiveModules_iff.2
      ⟨inferInstance, Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))⟩⟩

private theorem clopenRankPiece_obj (f : LocallyConstant (PrimeSpectrum R) ℕ) (k : ℕ) :
    (clopenRankPiece R f k).obj =
      ModuleCat.of R (Fin k → (clopenObj R (f.fiberClopens k)).obj) :=
  (rfl)

/-- On a nonnegative locally constant function `f : Spec R → ℕ`, the rank section produces the
class of the clopen-glued module `ClopenRankModule R f`. -/
theorem rankSection_map_natCast (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    rankSection R (f.map (Nat.cast : ℕ → ℤ)) = SplitK0.of.{u} (clopenRankObj R f) := by
  let s := f.range_finite.toFinset
  rw [rankSection_eq_sum_of_partition R _ s f.fiberClopens (Nat.cast : ℕ → ℤ)
    (f.pairwise_disjoint_fiberClopens.set_pairwise _) f.finset_sup_fiberClopens
    (fun _ _ _ hp ↦ congrArg (Nat.cast : ℕ → ℤ) (LocallyConstant.mem_fiberClopens.1 hp))]
  rw [SplitK0.of_eq_sum_of_linearEquiv_pi (X := clopenRankObj R f)
      (fun k : s ↦ clopenRankPiece R f k.val)
      ((eqToIso (clopenRankObj_obj R f)).toLinearEquiv.trans
        ((ClopenRankModule.equivPi R f).trans
          (LinearEquiv.piCongrRight fun k ↦
            (eqToIso (clopenRankPiece_obj R f k.val)).symm.toLinearEquiv))),
    ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SplitK0.of_eq_sum_of_linearEquiv_pi (X := clopenRankPiece R f k.val)
      (fun _ : Fin k.val ↦ clopenObj R (f.fiberClopens k.val))
      (eqToIso (clopenRankPiece_obj R f k.val)).toLinearEquiv,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← natCast_zsmul, clopenClass]

/-- **`rankSection R` is a right inverse to `rankHom R`.** -/
@[simp]
theorem rankHom_comp_rankSection :
    (rankHom R).comp (rankSection R) = RingHom.id _ := by
  ext g p
  simp only [RingHom.comp_apply, RingHom.id_apply, rankSection_apply, map_sum]
  rw [← LocallyConstant.evalRingHom_apply p, map_sum,
    Finset.sum_eq_single_of_mem (g p) (g.range_finite.mem_toFinset.2 ⟨p, rfl⟩)]
  · rw [map_zsmul, rankHom_clopenClass, map_zsmul, LocallyConstant.evalRingHom_apply]
    simp [LocallyConstant.coe_charFn]
  · intro n _ hne
    rw [map_zsmul, rankHom_clopenClass, map_zsmul, LocallyConstant.evalRingHom_apply]
    simp [LocallyConstant.coe_charFn, hne.symm]

@[simp]
theorem rankHom_rankSection (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    rankHom R (rankSection R g) = g :=
  DFunLike.congr_fun (rankHom_comp_rankSection R) g

theorem rankHom_surjective : Function.Surjective (rankHom R) :=
  Function.RightInverse.surjective (rankHom_rankSection R)

theorem rankSection_injective : Function.Injective (rankSection R) :=
  Function.LeftInverse.injective (rankHom_rankSection R)

/-- **Naturality of the rank section under scalar extension.** -/
theorem extend_comp_rankSection {S : Type u} [CommRing S] (f : R →+* S) :
    f.finiteProjectiveModulesSplitK0Extend.comp (rankSection R) =
      (rankSection S).comp
        (LocallyConstant.comapRingHom
          ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) := by
  ext g
  let φ : C(PrimeSpectrum S, PrimeSpectrum R) :=
    ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
  let g' : LocallyConstant (PrimeSpectrum S) ℤ := LocallyConstant.comapRingHom φ g
  let s := g.range_finite.toFinset
  let U : ℤ → Clopens (PrimeSpectrum S) := fun n ↦ (g.comap φ).fiberClopens n
  rw [RingHom.comp_apply, RingHom.comp_apply, rankSection_apply, map_sum,
    rankSection_eq_sum_of_partition S g' s U id
      ((g.comap φ).pairwise_disjoint_fiberClopens.set_pairwise _)
      ((g.comap φ).finset_sup_fiberClopens_of_forall_mem fun q ↦
        g.range_finite.mem_toFinset.2 ⟨φ q, rfl⟩)
      (fun _ _ _ hq ↦ LocallyConstant.mem_fiberClopens.1 hq)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [map_zsmul, extend_clopenClass R f (g.fiberClopens n), id_eq]
  exact congrArg (n • clopenClass S ·) (LocallyConstant.preimage_fiberClopens φ g n)

theorem extend_rankSection {S : Type u} [CommRing S] (f : R →+* S)
    (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    f.finiteProjectiveModulesSplitK0Extend (rankSection R g) =
      rankSection S (g.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) :=
  DFunLike.congr_fun (extend_comp_rankSection R f) g

end RankSection

/-! ### Reduced `K₀` and split exactness -/

section ReducedK0

variable (R : Type u) [CommRing R]

/-- **Reduced `K₀` of a commutative ring.** The ideal `reducedK0 R := ker(rankHom R)` of virtual
finitely generated projective modules of locally constant rank zero. -/
noncomputable def reducedK0 : Ideal (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :=
  RingHom.ker (rankHom R)

variable {R} in
@[simp]
theorem mem_reducedK0_iff {x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory} :
    x ∈ reducedK0 R ↔ rankHom R x = 0 :=
  Iff.rfl

/-- **Splitting of `K₀(proj R)`.** The rank homomorphism and its clopen section split
`K₀(proj R)` additively into `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`. -/
noncomputable def splitK0EquivProdReducedK0 :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R where
  toFun x := (rankHom R x, ⟨x - rankSection R (rankHom R x), by simp⟩)
  invFun p := rankSection R p.1 + p.2.val
  map_add' x y := Prod.ext (map_add (rankHom R) x y) (Subtype.ext <| by
    simp only [Prod.snd_add, Submodule.coe_add, map_add]; abel)
  left_inv x := by simp
  right_inv p := Prod.ext (by simp [mem_reducedK0_iff.1 p.2.property])
    (Subtype.ext <| by simp [mem_reducedK0_iff.1 p.2.property])

@[simp]
theorem splitK0EquivProdReducedK0_fst
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    (splitK0EquivProdReducedK0 R x).1 = rankHom R x := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_snd
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ((splitK0EquivProdReducedK0 R x).2 :
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) =
      x - rankSection R (rankHom R x) := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_symm_apply
    (p : LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R) :
    (splitK0EquivProdReducedK0 R).symm p = rankSection R p.1 + p.2.val := (rfl)

end ReducedK0

/-! ### Semilocal, localization-kernel, and PID classifications -/

section Classification

variable (R : Type u) [CommRing R]

/-- **General clopen-glued classification criterion.** If every finitely generated projective
`R`-module is isomorphic to its clopen-glued model
`ClopenRankModule R (Module.rankLocallyConstant R P.obj)`, then `rankSection R` is a left inverse
to `rankHom R`. -/
theorem rankSection_comp_rankHom_eq_id_of_forall_clopenRankModule
    (hiso : ∀ P : (finiteProjectiveModules R).FullSubcategory,
      Nonempty (P.obj ≃ₗ[R] ClopenRankModule R (Module.rankLocallyConstant R P.obj))) :
    (rankSection R).comp (rankHom R) = RingHom.id _ := by
  refine SplitK0.ringHom_ext fun P ↦ ?_
  obtain ⟨θ⟩ := hiso P
  rw [RingHom.comp_apply, RingHom.id_apply, rankHom_of, rankSection_map_natCast]
  exact (SplitK0.of_congr (ObjectProperty.isoMk _ θ.toModuleIso)).symm

/-- Whenever `rankSection R` is a left inverse to `rankHom R`, the reduced `K₀` ideal vanishes. -/
theorem reducedK0_eq_bot_of_rankSection_comp_rankHom
    (h : (rankSection R).comp (rankHom R) = RingHom.id _) :
    reducedK0 R = ⊥ :=
  eq_bot_iff.2 fun x hx ↦ by
    have hx' := DFunLike.congr_fun h x
    rw [RingHom.comp_apply, RingHom.id_apply, mem_reducedK0_iff.1 hx, map_zero] at hx'
    exact (Submodule.mem_bot _).2 hx'.symm

/-- Over a commutative semilocal ring, `rankSection R` is also a left inverse to `rankHom R`. -/
@[simp]
theorem rankSection_comp_rankHom_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    (rankSection R).comp (rankHom R) = RingHom.id _ :=
  rankSection_comp_rankHom_eq_id_of_forall_clopenRankModule R fun P ↦
    nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum (R := R) P.obj

@[simp]
theorem rankSection_rankHom_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rankSection R (rankHom R x) = x :=
  DFunLike.congr_fun (rankSection_comp_rankHom_of_finite_maximalSpectrum R) x

/-- **Semilocal `K₀` classification.** For a commutative semilocal ring `R`, the locally constant
rank homomorphism is a ring isomorphism
`K₀(proj R) ≃+* LocallyConstant (PrimeSpectrum R) ℤ`. -/
noncomputable def rankEquivOfFiniteMaximalSpectrum [Finite (MaximalSpectrum R)] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  RingEquiv.ofRingHom (rankHom R) (rankSection R)
    (rankHom_comp_rankSection R)
    (rankSection_comp_rankHom_of_finite_maximalSpectrum R)

@[simp]
theorem rankEquivOfFiniteMaximalSpectrum_apply [Finite (MaximalSpectrum R)]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    rankEquivOfFiniteMaximalSpectrum R x = rankHom R x := (rfl)

@[simp]
theorem rankEquivOfFiniteMaximalSpectrum_symm_apply [Finite (MaximalSpectrum R)]
    (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    (rankEquivOfFiniteMaximalSpectrum R).symm g = rankSection R g := (rfl)

theorem rankEquivOfFiniteMaximalSpectrum_of [Finite (MaximalSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivOfFiniteMaximalSpectrum R (SplitK0.of.{u} P) =
      (Module.rankLocallyConstant R P.obj).map (Nat.cast : ℕ → ℤ) :=
  rankHom_of R P

/-- The reduced `K₀` ideal of a commutative semilocal ring vanishes. -/
theorem reducedK0_eq_bot_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    reducedK0 R = ⊥ :=
  reducedK0_eq_bot_of_rankSection_comp_rankHom R
    (rankSection_comp_rankHom_of_finite_maximalSpectrum R)

/-- **Localization-kernel characterization of reduced `K₀`.** A class in `K₀(proj R)` has rank
zero everywhere on `Spec R` if and only if it maps to zero in `K₀(proj R_p)` at every prime `p`. -/
theorem mem_reducedK0_iff_forall_localization
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    x ∈ reducedK0 R ↔
      ∀ p : PrimeSpectrum R,
        (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x =
          0 := by
  refine ⟨fun hx p ↦ ?_, fun hloc ↦ ?_⟩
  · have hmem :
        (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x ∈
          reducedK0 (Localization.AtPrime p.asIdeal) :=
      mem_reducedK0_iff.2 <| by
        ext q
        rw [rankHom_extend_apply, mem_reducedK0_iff.1 hx, LocallyConstant.zero_apply,
          LocallyConstant.zero_apply]
    rwa [reducedK0_eq_bot_of_finite_maximalSpectrum] at hmem
  · rw [mem_reducedK0_iff]
    ext p
    have h := congrFun (congrArg DFunLike.coe (congrArg
      (rankHom (Localization.AtPrime p.asIdeal)) (hloc p)))
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal))
    have hpt : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)) = p :=
      PrimeSpectrum.ext
        (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal)
    rwa [rankHom_extend_apply, hpt, map_zero] at h

/-- If every finitely generated projective `R`-module is free, then `rankSection R` is a left
inverse to `rankHom R`. -/
theorem rankSection_comp_rankHom_of_forall_free
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    (rankSection R).comp (rankHom R) = RingHom.id _ := by
  refine rankSection_comp_rankHom_eq_id_of_forall_clopenRankModule R fun P ↦ ?_
  have := hfree P
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R P.obj
    have := Module.subsingleton R (ClopenRankModule R (Module.rankLocallyConstant R P.obj))
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · have hconst : Module.rankLocallyConstant R P.obj =
        LocallyConstant.const (PrimeSpectrum R) (Module.finrank R P.obj) := by
      ext p
      rw [Module.rankLocallyConstant_apply]
      exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P.obj)) p
    exact ⟨(Module.finBasis R P.obj).equivFun.trans <|
      (ClopenRankModule.constEquiv R (Module.finrank R P.obj)).symm.trans <|
        ClopenRankModule.equivOfEq R hconst.symm⟩

/-- If every finitely generated projective `R`-module is free, then the reduced `K₀` ideal of `R`
vanishes. -/
theorem reducedK0_eq_bot_of_forall_free
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    reducedK0 R = ⊥ :=
  reducedK0_eq_bot_of_rankSection_comp_rankHom R
    (rankSection_comp_rankHom_of_forall_free R hfree)

private theorem connectedSpace_primeSpectrum_of_forall_free' [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    ConnectedSpace (PrimeSpectrum R) :=
  TauCeti.connectedSpace_primeSpectrum_of_forall_free R fun P _ _ _ _ ↦
    hfree ⟨ModuleCat.of R P, finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

/-- If `R` is nontrivial and every finitely generated projective `R`-module is free, then stalk
rank gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfForallFree [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  haveI := connectedSpace_primeSpectrum_of_forall_free' R hfree
  (RingEquiv.ofRingHom (rankHom R) (rankSection R)
    (rankHom_comp_rankSection R) (rankSection_comp_rankHom_of_forall_free R hfree)).trans
    (LocallyConstant.constRingEquiv (PrimeSpectrum R) ℤ).symm

@[simp]
theorem rankEquivIntOfForallFree_of [Nontrivial R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfForallFree R hfree (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) := by
  have := connectedSpace_primeSpectrum_of_forall_free' R hfree
  have := hfree P
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  rw [rankEquivIntOfForallFree, RingEquiv.trans_apply, RingEquiv.ofRingHom_apply,
    LocallyConstant.constRingEquiv_symm_apply _ _ _ p₀, rankHom_of_free,
    LocallyConstant.coe_const, Function.const_apply]

/-- **Connected semilocal / local `K₀` classification.** Over a commutative semilocal ring with
connected prime spectrum (in particular, over any commutative local ring), stalk rank gives a ring
isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfFiniteMaximalSpectrum
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  rankEquivIntOfForallFree R fun P ↦ free_of_finite_maximalSpectrum_of_preconnectedSpace P.obj

@[simp]
theorem rankEquivIntOfFiniteMaximalSpectrum_of
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfFiniteMaximalSpectrum R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) :=
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  rankEquivIntOfForallFree_of R _ P

/-- **PID `K₀` classification.** Over a principal ideal domain `R`, every finitely generated
projective module is free, so stalk rank gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfIsPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  rankEquivIntOfForallFree R fun _ ↦ Module.free_of_finite_type_torsion_free'

@[simp]
theorem rankEquivIntOfIsPrincipalIdealRing_of [IsDomain R] [IsPrincipalIdealRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfIsPrincipalIdealRing R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) :=
  rankEquivIntOfForallFree_of R _ P

end Classification

end TauCeti.FiniteProjectiveModules

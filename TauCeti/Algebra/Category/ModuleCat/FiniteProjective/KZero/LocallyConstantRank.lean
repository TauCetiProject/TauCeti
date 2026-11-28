/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Clopen
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Rank
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Ring
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Semilocal

import TauCeti.Order.Disjoint
import TauCeti.RingTheory.Idempotents.Clopen.Basic
import TauCeti.RingTheory.Idempotents.Module
import TauCeti.Topology.LocallyConstant.Algebra
import TauCeti.Topology.LocallyConstant.CharFn

/-!
# Reduced `K₀`, clopen section naturality, and semilocal / PID rank classifications

Building on the locally constant rank homomorphism `TauCeti.FiniteProjectiveModules.rank` and its
section `TauCeti.FiniteProjectiveModules.rankSection` from
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.StalkRank`, this file records:

* Naturality of `rank` and `rankSection` under the ring-homomorphism scalar extension
  `RingHom.finiteProjectiveModulesSplitK0Extend`, together with partition formulas and the
  realization of `rankSection` on `ℕ`-valued functions via `TauCeti.ClopenRankModule`.
* The reduced `K₀` ideal `TauCeti.FiniteProjectiveModules.reducedK0 R := RingHom.ker (rank R)` and
  the additive splitting `TauCeti.FiniteProjectiveModules.splitK0EquivProdReducedK0` of
  `K₀(proj R)` into `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`.
* Vanishing of `reducedK0 R` for semilocal rings and rings whose finitely generated projective
  modules are stably free, the integer ring isomorphism
  `TauCeti.FiniteProjectiveModules.rankEquivIntOfFiniteMaximalSpectrum` for connected semilocal
  rings, and stalk-rank evaluation of the stably free and PID ring isomorphisms from `KZero.Ring`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.reducedK0`: the ideal `RingHom.ker (rank R)` of rank-zero
  classes, together with the splitting `splitK0EquivProdReducedK0`.
* `TauCeti.FiniteProjectiveModules.rankEquivIntOfFiniteMaximalSpectrum`: the ring isomorphism
  `K₀(proj R) ≃+* ℤ` for a commutative semilocal ring with connected prime spectrum (including all
  commutative local rings).

## Main results

* `TauCeti.FiniteProjectiveModules.rank_comp_extend` and
  `TauCeti.FiniteProjectiveModules.extend_comp_rankSection`: naturality of `rank` and
  `rankSection` under `RingHom.finiteProjectiveModulesSplitK0Extend`.
* `TauCeti.FiniteProjectiveModules.rankSection_eq_sum_of_partition` and
  `TauCeti.FiniteProjectiveModules.rankSection_map_natCast`: partition and clopen-glued module
  formulas for `rankSection`.
* `TauCeti.FiniteProjectiveModules.reducedK0_eq_bot_of_rankSection_comp_rank`: kernel vanishing
  when `rankSection R` is a left inverse to `rank R`.
* `TauCeti.FiniteProjectiveModules.reducedK0_eq_bot_of_finite_maximalSpectrum` and
  `reducedK0_eq_bot_of_forall_isStablyFree`: vanishing of reduced `K₀` for semilocal rings and rings
  whose finitely generated projective modules are stably free.
* `TauCeti.FiniteProjectiveModules.rankEquivIntOfForallIsStablyFree_apply`,
  `rankEquivIntOfFiniteMaximalSpectrum_apply`, and `rankEquivIntOfIsPrincipalIdealRing_apply`:
  evaluation of the integer rank equivalences via `rank`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Lemmas 2.2–2.3 and Corollary 2.6.2, pp. 71–75.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §§1.1–1.3.
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open PrimeSpectrum (isIdempotentElemEquivClopens)

universe u

namespace TauCeti.FiniteProjectiveModules

section Rank

variable (R : Type u) [CommRing R]

theorem rank_of_free (P : (finiteProjectiveModules R).FullSubcategory) [Module.Free R P.obj] :
    rank R (SplitK0.of.{u} P) =
      LocallyConstant.const (PrimeSpectrum R) (Module.finrank R P.obj : ℤ) := by
  ext p
  simp [congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P.obj)) p]

/-- **Naturality of rank under scalar extension.** For `f : R →+* S`, rank commutes with scalar
extension along `f` and pullback of locally constant functions along `Spec S → Spec R`. -/
theorem rank_comp_extend {S : Type u} [CommRing S] (f : R →+* S) :
    (rank S).comp f.finiteProjectiveModulesSplitK0Extend =
      (LocallyConstant.comapRingHom ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).comp
        (rank R) :=
  RingHom.ext fun x ↦ by
    ext p
    simp [RingHom.finiteProjectiveModulesSplitK0Extend_apply, rank_map]

@[simp]
theorem rank_extend_apply {S : Type u} [CommRing S] (f : R →+* S)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (q : PrimeSpectrum S) :
    rank S (f.finiteProjectiveModulesSplitK0Extend x) q = rank R x (q.comap f) :=
  DFunLike.congr_fun (DFunLike.congr_fun (rank_comp_extend R f) x) q

end Rank

/-! ### Clopen projective classes and the rank section -/

section RankSection

variable (R : Type u) [CommRing R]

@[simp]
theorem of_clopenProjective_bot : SplitK0.of.{u} (clopenProjective R ⊥) = 0 := by
  have : Subsingleton ((finiteProjectiveModules R).ι.obj (clopenProjective R ⊥)) := by
    rw [ObjectProperty.ι_obj, clopenProjective_obj,
      PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot, sub_zero, Ideal.span_singleton_one]
    infer_instance
  exact SplitK0.of_eq_zero_of_isZero (Limits.IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules R).ι (clopenProjective R ⊥) (ModuleCat.isZero_of_subsingleton _))

theorem of_clopenProjective_sup_of_disjoint {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    SplitK0.of.{u} (clopenProjective R (U ⊔ V)) =
      SplitK0.of.{u} (clopenProjective R U) + SplitK0.of.{u} (clopenProjective R V) := by
  let eU := (isIdempotentElemEquivClopens.symm U).property
  let eV := (isIdempotentElemEquivClopens.symm V).property
  let eUV := (isIdempotentElemEquivClopens.symm (U ⊔ V)).property
  refine SplitK0.of_eq_add_of_linearEquiv_prod (X := clopenProjective R (U ⊔ V))
    (P := clopenProjective R U) (Q := clopenProjective R V) ?_
  exact (eqToIso (clopenProjective_obj R (U ⊔ V))).toLinearEquiv.trans <|
    eUV.spanSingletonEquivQuotientOneSub.symm.trans <|
      (LinearEquiv.ofEq _ _ (by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_sup_of_disjoint h])).trans <|
        (eU.spanSingletonAddEquivProd eV
          (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h)
          (PrimeSpectrum.isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h.symm)).trans <|
          LinearEquiv.prodCongr
            (eU.spanSingletonEquivQuotientOneSub.trans
              (eqToIso (clopenProjective_obj R U)).symm.toLinearEquiv)
            (eV.spanSingletonEquivQuotientOneSub.trans
              (eqToIso (clopenProjective_obj R V)).symm.toLinearEquiv)

theorem of_clopenProjective_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : (s : Set ι).PairwiseDisjoint U) :
    SplitK0.of.{u} (clopenProjective R (s.sup U)) =
      ∑ i ∈ s, SplitK0.of.{u} (clopenProjective R (U i)) :=
  hdisj.map_finset_sup (fun V ↦ SplitK0.of.{u} (clopenProjective R V))
    (of_clopenProjective_bot R) fun _ _ h ↦ of_clopenProjective_sup_of_disjoint R h

theorem extend_clopenProjective {S : Type u} [CommRing S] (f : R →+* S)
    (U : Clopens (PrimeSpectrum R)) :
    f.finiteProjectiveModulesSplitK0Extend (SplitK0.of.{u} (clopenProjective R U)) =
      SplitK0.of.{u} (clopenProjective S
        (Clopens.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ U)) :=
  (RingHom.finiteProjectiveModulesSplitK0Extend_of f _).trans
    (SplitK0.of_extendScalars_obj (balancedExtensionClopenProjectiveEquiv f U))

/-- `rankSection R g` is computed by any finite clopen partition of `Spec R` on which `g` is
constant on each piece. -/
theorem rankSection_eq_sum_of_partition (g : LocallyConstant (PrimeSpectrum R) ℤ)
    {ι : Type*} (s : Finset ι) (U : ι → Clopens (PrimeSpectrum R)) (c : ι → ℤ)
    (hdisj : (s : Set ι).PairwiseDisjoint U) (hcover : s.sup U = ⊤)
    (hval : ∀ i ∈ s, ∀ p ∈ U i, g p = c i) :
    rankSection R g = ∑ i ∈ s, c i • SplitK0.of.{u} (clopenProjective R (U i)) := by
  rw [LocallyConstant.eq_sum_charFn_of_partition g s U c hdisj hcover hval, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, rankSection_charFn]

@[simp]
theorem rankSection_const (n : ℤ) :
    rankSection R (LocallyConstant.const (PrimeSpectrum R) n) = n := by
  simpa [LocallyConstant.intCast_eq_const] using map_intCast (rankSection R) n

/-- The finite-projective object `R ⧸ (1 - e_{f⁻¹{k}})` repeated `k` times for a rank fiber `k`. -/
private noncomputable def clopenRankPiece (f : LocallyConstant (PrimeSpectrum R) ℕ) (k : ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Fin k → (clopenProjective R (f.fiberClopens k)).obj),
    finiteProjectiveModules_iff.2
      ⟨inferInstance, Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))⟩⟩

private theorem clopenRankPiece_obj (f : LocallyConstant (PrimeSpectrum R) ℕ) (k : ℕ) :
    (clopenRankPiece R f k).obj =
      ModuleCat.of R (Fin k → (clopenProjective R (f.fiberClopens k)).obj) :=
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
            (LinearEquiv.piCongrRight fun _ ↦
              (isIdempotentElemEquivClopens.symm
                (f.fiberClopens k.val)).property.spanSingletonEquivQuotientOneSub.trans
                (eqToIso (clopenProjective_obj R (f.fiberClopens k.val))).symm.toLinearEquiv).trans
              (eqToIso (clopenRankPiece_obj R f k.val)).symm.toLinearEquiv))),
    ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SplitK0.of_eq_sum_of_linearEquiv_pi (X := clopenRankPiece R f k.val)
      (fun _ : Fin k.val ↦ clopenProjective R (f.fiberClopens k.val))
      (eqToIso (clopenRankPiece_obj R f k.val)).toLinearEquiv,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← natCast_zsmul]

/-- **Naturality of the rank section under scalar extension.** -/
theorem extend_comp_rankSection {S : Type u} [CommRing S] (f : R →+* S) :
    f.finiteProjectiveModulesSplitK0Extend.comp (rankSection R) =
      (rankSection S).comp
        (LocallyConstant.comapRingHom
          ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) :=
  RingHom.ext fun g ↦ by
    simp only [RingHom.comp_apply, RingHom.finiteProjectiveModulesSplitK0Extend_apply,
      map_rankSection]
    exact congrArg (rankSection S) (LocallyConstant.ext fun _ ↦ rfl)

theorem extend_rankSection {S : Type u} [CommRing S] (f : R →+* S)
    (g : LocallyConstant (PrimeSpectrum R) ℤ) :
    f.finiteProjectiveModulesSplitK0Extend (rankSection R g) =
      rankSection S (g.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩) :=
  DFunLike.congr_fun (extend_comp_rankSection R f) g

end RankSection

/-! ### Reduced `K₀` and split exactness -/

section ReducedK0

variable (R : Type u) [CommRing R]

/-- **Reduced `K₀` of a commutative ring.** The ideal `reducedK0 R := ker(rank R)` of virtual
finitely generated projective modules of locally constant rank zero. -/
noncomputable def reducedK0 : Ideal (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :=
  RingHom.ker (rank R)

variable {R} in
@[simp]
theorem mem_reducedK0_iff {x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory} :
    x ∈ reducedK0 R ↔ rank R x = 0 :=
  Iff.rfl

variable {R} in
/-- A class lies in `reducedK0 R` if and only if its scalar extension along the canonical ring
homomorphism to `Localization.AtPrime p.asIdeal` vanishes for every prime `p`. -/
theorem mem_reducedK0_iff_forall_localization
    {x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory} :
    x ∈ reducedK0 R ↔ ∀ p : PrimeSpectrum R,
      (algebraMap R (Localization.AtPrime p.asIdeal)).finiteProjectiveModulesSplitK0Extend x =
        0 := by
  simpa [RingHom.finiteProjectiveModulesSplitK0Extend_apply] using
    rank_eq_zero_iff_forall_map_eq_zero x

/-- **Splitting of `K₀(proj R)`.** The rank homomorphism and its clopen section split
`K₀(proj R)` additively into `LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R`. -/
noncomputable def splitK0EquivProdReducedK0 :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R where
  toFun x := (rank R x, ⟨x - rankSection R (rank R x), by simp⟩)
  invFun p := rankSection R p.1 + p.2.val
  map_add' x y := Prod.ext (map_add (rank R) x y) (Subtype.ext <| by
    simp only [Prod.snd_add, Submodule.coe_add, map_add]; abel)
  left_inv x := by simp
  right_inv p := Prod.ext (by simp [mem_reducedK0_iff.1 p.2.property])
    (Subtype.ext <| by simp [mem_reducedK0_iff.1 p.2.property])

@[simp]
theorem splitK0EquivProdReducedK0_fst
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    (splitK0EquivProdReducedK0 R x).1 = rank R x := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_snd
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ((splitK0EquivProdReducedK0 R x).2 :
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) =
      x - rankSection R (rank R x) := (rfl)

@[simp]
theorem splitK0EquivProdReducedK0_symm_apply
    (p : LocallyConstant (PrimeSpectrum R) ℤ × reducedK0 R) :
    (splitK0EquivProdReducedK0 R).symm p = rankSection R p.1 + p.2.val := (rfl)

end ReducedK0

/-! ### Semilocal and stably free classifications -/

section Classification

variable (R : Type u) [CommRing R]

/-- Whenever `rankSection R` is a left inverse to `rank R`, the reduced `K₀` ideal vanishes. -/
theorem reducedK0_eq_bot_of_rankSection_comp_rank
    (h : (rankSection R).comp (rank R) = RingHom.id _) :
    reducedK0 R = ⊥ :=
  eq_bot_iff.2 fun x hx ↦ by
    have hx' := DFunLike.congr_fun h x
    rw [RingHom.comp_apply, RingHom.id_apply, mem_reducedK0_iff.1 hx, map_zero] at hx'
    exact (Submodule.mem_bot _).2 hx'.symm

/-- The reduced `K₀` ideal of a commutative semilocal ring vanishes. -/
theorem reducedK0_eq_bot_of_finite_maximalSpectrum [Finite (MaximalSpectrum R)] :
    reducedK0 R = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (rank_injective R)

/-- If every finitely generated projective `R`-module is stably free, then `rankSection R` is a
left inverse to `rank R`. -/
theorem rankSection_comp_rank_of_forall_isStablyFree
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj) :
    (rankSection R).comp (rank R) = RingHom.id _ := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact RingHom.ext fun _ ↦ Subsingleton.elim _ _
  · refine RingHom.ext fun x ↦ ?_
    obtain ⟨z, rfl⟩ := exists_zsmul_of_finiteProjectiveModulesRegular_eq R h x
    rw [RingHom.comp_apply, RingHom.id_apply, splitK0_of_finiteProjectiveModulesRegular R,
      zsmul_one, map_intCast, map_intCast]

/-- If every finitely generated projective `R`-module is stably free, then the reduced `K₀` ideal
of `R` vanishes. -/
theorem reducedK0_eq_bot_of_forall_isStablyFree
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj) :
    reducedK0 R = ⊥ :=
  reducedK0_eq_bot_of_rankSection_comp_rank R
    (rankSection_comp_rank_of_forall_isStablyFree R h)

theorem rankEquivIntOfForallIsStablyFree_apply [Nontrivial R]
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankEquivIntOfForallIsStablyFree R h x = rank R x p := by
  obtain ⟨z, rfl⟩ := exists_zsmul_of_finiteProjectiveModulesRegular_eq R h x
  simp [splitK0_of_finiteProjectiveModulesRegular R, LocallyConstant.intCast_eq_const]

/-- Over a commutative semilocal ring with connected prime spectrum, every finitely generated
projective module is stably free. -/
theorem forall_isStablyFree_of_finite_maximalSpectrum
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) : Module.IsStablyFree R P.obj :=
  have : Module.Free R P.obj := Module.free_of_connectedSpace_of_finite_maximalSpectrum
  inferInstance

/-- **Connected semilocal / local `K₀` classification.** Over a commutative semilocal ring with
connected prime spectrum (in particular, over any commutative local ring), stalk rank gives a ring
isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfFiniteMaximalSpectrum
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  rankEquivIntOfForallIsStablyFree R (forall_isStablyFree_of_finite_maximalSpectrum R)

theorem rankEquivIntOfFiniteMaximalSpectrum_apply
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankEquivIntOfFiniteMaximalSpectrum R x = rank R x p :=
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  rankEquivIntOfForallIsStablyFree_apply R (forall_isStablyFree_of_finite_maximalSpectrum R) x p

@[simp]
theorem rankEquivIntOfFiniteMaximalSpectrum_of
    [Finite (MaximalSpectrum R)] [ConnectedSpace (PrimeSpectrum R)]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfFiniteMaximalSpectrum R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) :=
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  haveI : Module.Free R P.obj := Module.free_of_connectedSpace_of_finite_maximalSpectrum
  rankEquivIntOfForallIsStablyFree_of R (forall_isStablyFree_of_finite_maximalSpectrum R) P

theorem rankEquivIntOfIsPrincipalIdealRing_apply [IsDomain R] [IsPrincipalIdealRing R]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) (p : PrimeSpectrum R) :
    rankEquivIntOfIsPrincipalIdealRing R x = rank R x p := by
  rw [rankEquivIntOfIsPrincipalIdealRing_eq]
  exact rankEquivIntOfForallIsStablyFree_apply R (forall_isStablyFree_of_isPrincipalIdealRing R) x p

end Classification

end TauCeti.FiniteProjectiveModules

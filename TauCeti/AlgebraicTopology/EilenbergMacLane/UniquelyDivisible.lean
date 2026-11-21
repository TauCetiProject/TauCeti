/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
public import TauCeti.AlgebraicTopology.Singular.Reduced
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Eilenberg--Mac Lane spaces of uniquely divisible groups

Let `m : ℤ`, let `A` be an abelian group on which multiplication by `m` is bijective, and let
`n ≥ 1`. Then every Eilenberg--Mac Lane space `X` of type `K(A, n)` (with no hypothesis of CW
type) satisfies:

* multiplication by `m` is bijective on positive-degree integral singular homology `Hᵢ(X; ℤ)`
  (`TauCeti.IsEilenbergMacLaneSpace.bijective_zsmul_singularHomology_int_of_bijective_zsmul`);
* for any ring `R` and any `R`-module `M` annihilated by `m`, the positive-degree singular homology
  `Hᵢ(X; M)` vanishes
  (`TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`) and the reduced
  singular homology with coefficients in `M` vanishes in every degree
  (`TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_bijective_zsmul`);
* in particular, for any ring `k` in which `m = 0` (with no commutativity or semisimplicity
  assumption, including `ZMod m` for any `m : ℕ`), `Hᵢ(X; k)` vanishes for all `i > 0`
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`, and the
  multiplicative `[CommGroup G]` form
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zpow`);
* every Serre fibration with `K(A, n)` fibres induces isomorphisms on `k`-homology in every degree
  (`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber_of_bijective_zsmul`);
* for `m = 2`: every `K(A, n)` space of a uniquely two-divisible group has the mod-two homology of
  a point (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`
  and `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_isUniquelyTwoDivisible`).

The proof proceeds in three stages. First, for a commutative semisimple ring `k` with `m = 0`, the
base case `n = 1` is the computation of the group homology of `A`
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`), and the
induction on `n` goes through the based path fibration `p : P → X`
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).
Second, applying this at each prime divisor `p ∣ m` together with the prime-factor criterion
(`TopCat.isZero_singularHomology_zmod_iff_forall_prime`) and the mod-`m` coefficient sequence yields
bijectivity of multiplication by `m` on `Hᵢ(X; ℤ)`. Third, for any path-connected space whose
positive integral homology is uniquely `m`-divisible, the endomorphism
`m • id + (1 - m) • (π ≫ ι)` of the projective chain complex `C_*(X; ℤ)` is a quasi-isomorphism,
hence a chain homotopy equivalence; tensoring with any `ℤ`-module `M` killed by `m` kills
`Hᵢ(X; M)` for all `i > 0`, and restriction of scalars along `ℤ →+* R` transfers this to arbitrary
`R`-modules.

This is the input on Eilenberg--Mac Lane spaces for Serre's mod-`m` and mod-two vanishing theorems.

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.bijective_zsmul_singularHomology_int_of_bijective_zsmul`:
  unique `m`-divisibility of the positive-degree integral singular homology of `K(A, n)`.
* `TauCeti.IsEilenbergMacLaneSpace.isZero_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_bijective_zsmul`:
  vanishing of positive-degree and reduced singular homology of `K(A, n)` with coefficients in any
  module annihilated by `m`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zpow`: a `K(A, n)`
  (or multiplicatively `K(G, n)`) space of a uniquely `m`-divisible abelian group is acyclic modulo
  `m` over any ring `k` with `(m : k) = 0`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomology_of_isUniquelyTwoDivisible`: a
  `K(A, n)` space of a uniquely two-divisible abelian group has the mod-two homology of a point.
* `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber_of_bijective_zsmul`: a Serre
  fibration whose fibres are `K(A, n)` spaces of a uniquely `m`-divisible abelian group is a
  homology isomorphism over any ring `k` in which `m = 0`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1,
  Proposition 4.21, and Section 4.2, Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace TauCeti

namespace IsEilenbergMacLaneSpace

/-- Mod-`m` acyclicity of `K(A, d)` spaces for arbitrary `m : ℕ`, obtained from prime moduli via
`TopCat.isZero_singularHomology_zmod_iff_forall_prime`. -/
private theorem subsingleton_singularHomology_zmod_of_bijective_zsmul {m : ℕ} {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ (m : ℤ) • a) {d : ℕ} [NeZero d]
    {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x) (n : ℕ) :
    Subsingleton (((singularChains (ZMod m)).obj (TopCat.of X)).homology (n + 1)) := by
  by_cases hm : m = 0
  · subst hm
    have : Subsingleton A := ⟨fun a b ↦ hA.1 (by simp)⟩
    have hπ (r : ℕ) : Subsingleton (HomotopyGroup (Fin r) X x) := by
      by_cases hr : r = d
      · subst hr
        exact (hX.nonempty_homotopyGroupMulEquiv.some.toEquiv.trans
          Multiplicative.toAdd).subsingleton
      · exact hX.subsingleton_homotopyGroup hr
    exact ModuleCat.isZero_iff_subsingleton.1 <|
      isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup (fun r _ ↦ hπ r) (ZMod 0)
        (Nat.succ_ne_zero n) (Nat.lt_succ_self (n + 1))
  · have : NeZero m := ⟨hm⟩
    refine ModuleCat.isZero_iff_subsingleton.1 <|
      ((TopCat.of X).isZero_singularHomology_uliftZMod_iff m (n + 1)).1 <|
        ((TopCat.of X).isZero_singularHomology_zmod_iff_forall_prime m (n + 1)).2 fun p hp hpm ↦ ?_
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨q, rfl⟩ := hpm
    have hAp : Function.Bijective fun a : A ↦ (p : ℤ) • a := by
      have h1 : (fun a : A ↦ ((p * q : ℕ) : ℤ) • a) =
          (fun a : A ↦ (p : ℤ) • a) ∘ (fun a : A ↦ (q : ℤ) • a) := by
        funext a; rw [Function.comp_apply, Nat.cast_mul, mul_zsmul]
      have h2 : (fun a : A ↦ ((p * q : ℕ) : ℤ) • a) =
          (fun a : A ↦ (q : ℤ) • a) ∘ (fun a : A ↦ (p : ℤ) • a) := by
        funext a; rw [Function.comp_apply, Nat.cast_mul, mul_comm, mul_zsmul]
      exact ⟨Function.Injective.of_comp (h2 ▸ hA.1), Function.Surjective.of_comp (h1 ▸ hA.2)⟩
    exact ((TopCat.of X).isZero_singularHomology_uliftZMod_iff p (n + 1)).2 <|
      ModuleCat.isZero_iff_subsingleton.2 <|
        subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne (ZMod p)
          (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul (ZMod p)
            (m := p) (by simp) hAp) hX n

/-- Multiplication by `m : ℤ` is bijective on an abelian group iff multiplication by `m.natAbs`
is. -/
private lemma bijective_zsmul_iff_natAbs {M : Type*} [AddCommGroup M] (m : ℤ) :
    (Function.Bijective fun x : M ↦ m • x) ↔ Function.Bijective fun x : M ↦ (m.natAbs : ℤ) • x := by
  rcases Int.natAbs_eq m with h | h
  · rw [← h]
  · have hfun : (fun x : M ↦ m • x) = (fun x : M ↦ -x) ∘ (fun x : M ↦ (m.natAbs : ℤ) • x) := by
      funext x
      conv_lhs => rw [h]
      rw [Function.comp_apply, neg_zsmul]
    rw [hfun, Function.Bijective.of_comp_iff' neg_involutive.bijective]

/-- **Unique `m`-divisibility of the integral homology of `K(A, d)`**: if multiplication by `m : ℤ`
is a bijection of `A`, then for every `d ≥ 1` and `n ≥ 0`, multiplication by `m` is a bijection on
the integral singular homology `Hₙ₊₁(K(A, d); ℤ)`. -/
theorem bijective_zsmul_singularHomology_int_of_bijective_zsmul {m : ℤ} {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x)
    (n : ℕ) :
    Function.Bijective fun y : ((singularChains ℤ).obj (TopCat.of X)).homology (n + 1) ↦
      m • y := by
  rw [bijective_zsmul_iff_natAbs] at hA ⊢
  have hZ (j : ℕ) := ((TopCat.of X).isZero_singularHomology_uliftZMod_iff m.natAbs (j + 1)).2 <|
    ModuleCat.isZero_iff_subsingleton.2
      (subsingleton_singularHomology_zmod_of_bijective_zsmul hA hX j)
  have hbij := (TopCat.of X).bijective_zsmul_singularHomology_of_isZero_zmod m.natAbs (n + 1)
    (hZ n) (hZ (n + 1))
  let e : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of X) ≃+
      ((singularChains ℤ).obj (TopCat.of X)).homology (n + 1) :=
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso).app
        (TopCat.of X)).toLinearEquiv.toAddEquiv
  have hcomp : (fun y : ((singularChains ℤ).obj (TopCat.of X)).homology (n + 1) ↦
      (m.natAbs : ℤ) • y) = e ∘ (fun x ↦ (m.natAbs : ℤ) • x) ∘ e.symm := by
    funext y
    simp [map_zsmul]
  exact hcomp ▸ e.bijective.comp (hbij.comp e.symm.bijective)

/-- For a path-connected space `X` whose positive integral homology is uniquely `m`-divisible, the
endomorphism `m • id + (1 - m) • (π ≫ ι)` of the integral singular chain complex is a chain
homotopy equivalence. -/
private lemma homotopyEquivalences_zsmul_add_proj {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (m : ℤ)
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularChains ℤ).obj (TopCat.of X)).homology (q + 1) ↦ m • y) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ) (.down ℕ)
      (m • 𝟙 ((singularChains ℤ).obj (TopCat.of X)) +
        (1 - m) • ((singularChains ℤ).map (_root_.TopCat.isTerminalPUnit.from (TopCat.of X)) ≫
          (singularChains ℤ).map (TopCat.ofHom (ContinuousMap.const PUnit x)))) := by
  let p : TopCat.of X ⟶ TopCat.of PUnit := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.const PUnit x)
  let f : (singularChains ℤ).obj (TopCat.of X) ⟶ (singularChains ℤ).obj (TopCat.of X) :=
    m • 𝟙 _ + (1 - m) • ((singularChains ℤ).map p ≫ (singularChains ℤ).map s)
  have hqi : QuasiIso f := (quasiIso_iff f).2 fun q ↦ (quasiIsoAt_iff_isIso_homologyMap f q).2 <| by
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.down ℕ) q
    change IsIso (H.map f)
    rw [H.map_add, H.map_zsmul, H.map_zsmul, H.map_id]
    cases q with
    | zero =>
      have hps : H.map ((singularChains ℤ).map p ≫ (singularChains ℤ).map s) = 𝟙 _ := by
        rw [← (singularChains ℤ).map_comp]
        exact singularHomology₀_map_eq_id_of_pathConnectedSpace (ModuleCat.of ℤ ℤ) (p ≫ s)
      rw [hps, ← add_zsmul, add_sub_cancel, one_zsmul]
      infer_instance
    | succ q =>
      have hP : Limits.IsZero (H.obj ((singularChains ℤ).obj (TopCat.of PUnit))) :=
        isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℤ ℤ)
          (TopCat.of PUnit) q.succ_ne_zero
      rw [H.map_comp, hP.eq_of_tgt (H.map ((singularChains ℤ).map p)) 0, Limits.zero_comp,
        smul_zero, add_zero]
      exact (ConcreteCategory.isIso_iff_bijective _).2 (hX q)
  have : Projective (ModuleCat.of ℤ ℤ) := (ModuleCat.of ℤ ℤ).projective_of_categoryTheory_projective
  have (q : ℕ) : Projective (((singularChains ℤ).obj (TopCat.of X)).X q) :=
    Projective.of_iso (((_root_.TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
      (ModuleCat.of ℤ ℤ) q).coconePointUniqueUpToIso (Limits.coproductIsCoproduct _)).symm
      (inferInstanceAs (Projective (∐ fun _ :
        (_root_.TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk q)) ↦
          ModuleCat.of ℤ ℤ)))
  exact (ChainComplex.quasiIso_iff_of_projective f).1 hqi

/-- If `X` is path-connected and multiplication by `m` is bijective on every positive integral
singular homology group of `X`, then `H_{n + 1}(X; M) = 0` for every `ℤ`-module `M` annihilated by
`m`. -/
private theorem isZero_singularHomology_of_bijective_zsmul_int {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {m : ℤ}
    (hX : ∀ q : ℕ, Function.Bijective fun y :
      ((singularChains ℤ).obj (TopCat.of X)).homology (q + 1) ↦ m • y)
    (M : ModuleCat.{0} ℤ) (hmM : ∀ a : M, m • a = 0) (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj M).obj
      (TopCat.of X)) := by
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  let p : TopCat.of X ⟶ TopCat.of PUnit := _root_.TopCat.isTerminalPUnit.from (TopCat.of X)
  let s : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.const PUnit x)
  let f : (singularChains ℤ).obj (TopCat.of X) ⟶ (singularChains ℤ).obj (TopCat.of X) :=
    m • 𝟙 _ + (1 - m) • ((singularChains ℤ).map p ≫ (singularChains ℤ).map s)
  let F := MonoidalCategory.tensorLeft M
  let FCh := F.mapHomologicalComplex (.down ℕ)
  have hqi : QuasiIso (FCh.map f) :=
    (HomologicalComplex.mem_quasiIso_iff _).1 <|
      homotopyEquivalences_le_quasiIso _ _ _
        (F.homotopyEquivalences_mapHomologicalComplex_map f
          (homotopyEquivalences_zsmul_add_proj x m hX))
  have hiso : IsIso (HomologicalComplex.homologyMap (FCh.map f) (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap (FCh.map f) (n + 1)).1 ((quasiIso_iff _).1 hqi (n + 1))
  -- Multiplication by `m` kills `M`, hence kills every tensor product `M ⊗ N`.
  have hM0 : m • 𝟙 M = 0 := by ext a; exact hmM a
  have hkill : m • 𝟙 (FCh.obj ((singularChains ℤ).obj (TopCat.of X))) = 0 := by
    ext q : 1
    let G := MonoidalCategory.tensorRight (((singularChains ℤ).obj (TopCat.of X)).X q)
    change m • 𝟙 (G.obj M) = 0
    rw [← G.map_id, ← G.map_zsmul, hM0, G.map_zero]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.down ℕ) (n + 1)
  have hP : Limits.IsZero (H.obj (FCh.obj ((singularChains ℤ).obj (TopCat.of PUnit)))) :=
    (isZero_singularHomologyFunctor_of_contractibleSpace (F.obj (ModuleCat.of ℤ ℤ))
      (TopCat.of PUnit) n.succ_ne_zero).of_iso
        (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
          (TopCat.of PUnit)))
  have hzero : HomologicalComplex.homologyMap (FCh.map f) (n + 1) = 0 := by
    change H.map (FCh.map f) = 0
    rw [FCh.map_add, FCh.map_zsmul, FCh.map_id, hkill, zero_add, FCh.map_zsmul, FCh.map_comp,
      H.map_zsmul, H.map_comp, hP.eq_of_tgt (H.map (FCh.map ((singularChains ℤ).map p))) 0,
      Limits.zero_comp, smul_zero]
  have hFzero : Limits.IsZero
      ((FCh.obj ((singularChains ℤ).obj (TopCat.of X))).homology (n + 1)) :=
    (Limits.IsZero.iff_id_eq_zero _).2 <|
      (IsIso.hom_inv_id (HomologicalComplex.homologyMap (FCh.map f) (n + 1))).symm.trans <|
        (congrArg (· ≫ inv (HomologicalComplex.homologyMap (FCh.map f) (n + 1))) hzero).trans
          Limits.zero_comp
  exact (hFzero.of_iso
    (H.mapIso ((Functor.singularChainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
      (TopCat.of X))).symm).of_iso
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).mapIso
        (MonoidalCategory.rightUnitor M)).app (TopCat.of X)).symm

/-- **`K(A, d)` spaces of uniquely `m`-divisible groups are acyclic for any module killed by `m`.**
If multiplication by `m : ℤ` is a bijection of `A`, then for every `d ≥ 1`, every ring `R`, and
every `R`-module `M` annihilated by `m`, every `K(A, d)` space has vanishing positive-degree
singular homology `Hₙ₊₁(X; M) = 0`. -/
theorem isZero_singularHomology_of_bijective_zsmul {R : Type} [Ring R] (M : ModuleCat.{0} R)
    {m : ℤ} (hmM : ∀ a : M, m • a = 0) {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x) (n : ℕ) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} R) (n + 1)).obj M).obj
      (TopCat.of X)) := by
  have := hX.pathConnectedSpace
  let F := ModuleCat.restrictScalars.{0} (algebraMap ℤ R)
  have hℤ : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (F.obj M)).obj (TopCat.of X)) :=
    isZero_singularHomology_of_bijective_zsmul_int
      (bijective_zsmul_singularHomology_int_of_bijective_zsmul hA hX) (F.obj M) hmM n
  have hF : Limits.IsZero (F.obj (((singularHomologyFunctor (ModuleCat.{0} R) (n + 1)).obj M).obj
      (TopCat.of X))) :=
    hℤ.of_iso ((Functor.singularHomologyFunctorObjCompIso F M (n + 1)).app (TopCat.of X))
  have hsub : Subsingleton (F.obj (((singularHomologyFunctor (ModuleCat.{0} R) (n + 1)).obj M).obj
      (TopCat.of X))) :=
    ModuleCat.isZero_iff_subsingleton.1 hF
  exact ModuleCat.isZero_iff_subsingleton.2 hsub

/-- **Reduced acyclicity of `K(A, d)` spaces modulo `m`.** If multiplication by `m : ℤ` is a
bijection of `A`, then for every `d ≥ 1`, every ring `R`, and every `R`-module `M` annihilated by
`m`, the reduced singular homology of every `K(A, d)` space `X` with coefficients in `M` vanishes
in every degree, including degree zero. -/
theorem isZero_reducedSingularHomology_of_bijective_zsmul {R : Type} [Ring R]
    (M : ModuleCat.{0} R) {m : ℤ} (hmM : ∀ a : M, m • a = 0) {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {d : ℕ} [NeZero d] {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) d X x) (n : ℕ) :
    Limits.IsZero ((reducedSingularHomologyFunctor M n).obj (TopCat.of X)) := by
  cases n with
  | zero =>
    have := hX.pathConnectedSpace
    exact isZero_reducedSingularHomologyFunctor_zero _ _
  | succ n =>
    exact (isZero_singularHomology_of_bijective_zsmul M hmM hA hX n).of_iso
      ((reducedSingularHomologySuccIso M n).app (TopCat.of X))

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, n)`
space, for every `n ≥ 1`, has no homology in positive degrees with coefficients in any ring `k` in
which `m = 0` (including `ZMod m` for any `m : ℕ`). -/
theorem subsingleton_singularHomology_of_bijective_zsmul (k : Type) [Ring k] {m : ℤ}
    (hmk : (m : k) = 0) {A : Type} [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a)
    {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1 <|
    isZero_singularHomology_of_bijective_zsmul (ModuleCat.of k k)
      (fun a ↦ by rw [zsmul_eq_mul, hmk, zero_mul]) hA hX i

/-- Multiplicative form of `subsingleton_singularHomology_of_bijective_zsmul`: if raising to the
`m`-th power is a bijection of a commutative group `G`, then every `K(G, n)` space has no positive
degree homology with coefficients in any ring `k` in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zpow (k : Type) [Ring k] {m : ℤ}
    (hmk : (m : k) = 0) {G : Type} [CommGroup G] (hG : Function.Bijective fun g : G ↦ g ^ m)
    {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace G n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul k hmk (A := Additive G)
    (Additive.ofMul.bijective.comp (hG.comp Additive.toMul.bijective))
    (hX.of_mulEquiv (AddEquiv.toMultiplicativeRight (.refl (Additive G)))) i

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A`
and every `n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for
all `i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

/-- **Reduced mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group
`A` and every `n ≥ 1`, the reduced mod-two singular homology of every `K(A, n)` space vanishes in
every degree. -/
theorem isZero_reducedSingularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Limits.IsZero
      ((reducedSingularHomologyFunctor (ModuleCat.of (ZMod 2) (ZMod 2)) i).obj (TopCat.of X)) :=
  isZero_reducedSingularHomology_of_bijective_zsmul (ModuleCat.of (ZMod 2) (ZMod 2)) (m := 2)
    (fun a ↦ by rw [zsmul_eq_mul]; decide +revert)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

end IsEilenbergMacLaneSpace

/-- **A Serre fibration with `K(A, n)` fibres is a homology isomorphism modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then a Serre fibration
whose fibres are `K(A, n)` spaces, `n ≥ 1`, induces isomorphisms on homology with coefficients in
any ring `k` in which `m = 0`. -/
theorem isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber_of_bijective_zsmul
    (k : Type) [Ring k] {m : ℤ} (hmk : (m : k) = 0) {A : Type} [AddCommGroup A]
    (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {E B : _root_.TopCat.{0}}
    {p : E ⟶ B} (hp : TauCeti.TopCat.serreFibrations p)
    (hfib : ∀ b, ∃ y, IsEilenbergMacLaneSpace (Multiplicative A) n (p.fiber b) y) (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) i).obj (ModuleCat.of k k)).map p) :=
  TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber hp k i
    (fun b ↦ (hfib b).choose_spec.pathConnectedSpace) fun b q hq0 _ ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [singularHomologyFunctor_obj_obj]
      exact ModuleCat.isZero_iff_subsingleton.2
        (IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul k hmk hA
          (hfib b).choose_spec q)

end TauCeti

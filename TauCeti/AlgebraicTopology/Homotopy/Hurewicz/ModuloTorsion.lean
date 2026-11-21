/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.EilenbergMacLane.Torsion
import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# The Hurewicz theorem modulo localization torsion

Let `S : Submonoid ℤ` be a multiplicative submonoid of `ℤ` and `A` a localization of `ℤ` at `S`
(e.g. `S = nonZeroDivisors ℤ`, `A = ℚ` for torsion, or `S = Submonoid.powers d` for `d`-power
torsion). This file proves **Serre's Hurewicz theorem modulo `S`-torsion** (Serre 1953, Theorem 1)
for every simply connected topological space `Y`, together with its rational specialization.

## Proof outline

The proof builds a finite Whitehead tower over a CW approximation of `Y`, requiring no Hausdorff or
CW hypothesis on `Y`:
* Killing an `S`-torsion bottom homotopy group `π_{m + 2}(Z, z)` via `nConnectedCoverProj` has
  fibres `K(π_{m + 2}(Z, z), m + 1)`, which are `A`-acyclic; hence the cover induces an isomorphism
  on `H_*(-; A)`.
* Starting from the Hausdorff CW approximation `cwApproximation (TopCat.of Y) y → Y` and iterating
  `nConnectedCover` for degrees `2, …, n + 1` gives an `(n + 1)`-connected space `Z` with a map
  `q : Z → Y` bijective on `π_k` for `k ≥ n + 2` and inducing isomorphisms on `H_k(-; A)`.
* Comparing via naturality of `hurewiczIntLinearMap` against the integral Hurewicz isomorphism on
  `Z` yields the localized Hurewicz isomorphism in degree `n + 2`, and strong induction gives the
  reverse direction of the connectivity equivalence.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj`: killing an `S`-torsion bottom homotopy
  group induces an isomorphism on `H_*(-; A)`.
* `HomotopyGroup.bijective_hurewiczIntLinearMap_baseChange`,
  `HomotopyGroup.hurewiczLocalizationLinearEquiv`: the Hurewicz isomorphism after localization at
  `S`, natural in based maps (`HomotopyGroup.singularHomologyMap_hurewiczLocalizationLinearEquiv`).
* `HomotopyGroup.isTorsion'_ker_hurewiczIntLinearMap`,
  `HomotopyGroup.isTorsion'_quotient_range_hurewiczIntLinearMap`: kernel and cokernel of the
  integral Hurewicz map are `S`-torsion.
* `TauCeti.forall_isTorsion'_homotopyGroup_iff_singularHomology`,
  `TauCeti.forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology`: Serre's
  connectivity equivalence modulo `S`-torsion.
* `HomotopyGroup.hurewiczRatLinearEquiv`, `HomotopyGroup.hurewiczRatLinearEquivOfSubsingleton`,
  `TauCeti.forall_isAddTorsion_homotopyGroup_iff_singularHomology`,
  `TauCeti.forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat`: the rational Hurewicz theorem.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III, Theorem 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3, Whitehead towers.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.12.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory TensorProduct
open scoped Topology Topology.Homotopy

/-! ### One-step Whitehead cover and tower construction -/

namespace TauCeti

/-- **Killing an `S`-torsion bottom homotopy group is an `H_*(-; A)`-isomorphism.** Let `Z` be a
Hausdorff, `(m + 1)`-connected space whose homotopy group `π_{m + 2}(Z, z)` is `S`-torsion, and let
`A` be a localization of `ℤ` at `S`. Then the projection of the `(m + 2)`-connected cover
`Z⟨m + 2⟩ → Z` induces an isomorphism on `H_k(-; A)` for every `k : ℕ`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [PathConnectedSpace Z] (z : Z) (m : ℕ)
    (hZ : ∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k Z z))
    {S : Submonoid ℤ} (hπ : Module.IsTorsion' (Additive (π_ (m + 2) Z z)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] (k : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} A) k).obj (ModuleCat.of A A)).map
      (nConnectedCoverProj (m + 2) (TopCat.of Z) z)) :=
  isIso_singularHomologyMap_nConnectedCoverProj_of_fiber A (TopCat.of Z) z m hZ
    (fun hY i ↦ hY.subsingleton_singularHomology_of_isTorsion'_additive hπ A i) k

/-- **Finite Whitehead tower up to degree `n + 1`.** For any simply connected space `(Y, y)` whose
homotopy groups `π_{m + 2}(Y, y)` are `S`-torsion for `m < n`, and any localization `A` of `ℤ` at
`S`, there exists a Hausdorff `(n + 1)`-connected space `(Z, z)` and a based map `q : Z → Y` which
is bijective on `π_k` for `k ≥ n + 2` and induces isomorphisms on `H_k(-; A)` for all `k`. -/
private theorem exists_connected_cover_of_isTorsion' {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)] (S : Submonoid ℤ)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    ∀ (n : ℕ), (∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) →
      ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : T2Space Z) (_ : PathConnectedSpace Z)
        (z : Z) (q : C(Z, Y)) (hqz : q z = y),
        (∀ k < n + 2, Subsingleton (π_ k Z z)) ∧
        (∀ k, n + 2 ≤ k → Function.Bijective (HomotopyGroup.map (N := Fin k) q hqz)) ∧
        (∀ k, IsIso (HomologicalComplex.homologyMap ((singularChains A).map (TopCat.ofHom q)) k))
  | 0, _ => by
    let q := (cwApproximationMap (TopCat.of Y) y).hom
    have hqz := cwApproximationMap_cwApproximationBasepoint (TopCat.of Y) y
    refine ⟨cwApproximation (TopCat.of Y) y, inferInstance, inferInstance, inferInstance,
      cwApproximationBasepoint (TopCat.of Y) y, q, hqz, fun k hk ↦ ?_, fun k hk ↦ ?_,
      fun k ↦ (isWeakHomotopyEquivalence_cwApproximationMap _ _).isIso_singularHomologyMap
        (ModuleCat.of A A) k⟩
    · match k with
      | 0 => exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero _).1 inferInstance
      | 1 => exact ((HomotopyGroup.bijective_map_congr rfl rfl hqz).mp
          (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y 0 _)).1.subsingleton
      | k + 2 => omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (HomotopyGroup.bijective_map_congr rfl rfl hqz).mp
        (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y j _)
  | n + 1, hπ => by
    obtain ⟨Z, _, _, _, z, q, hqz, hZconn, hZbij, hZiso⟩ :=
      exists_connected_cover_of_isTorsion' y S A n fun m hm ↦ hπ m (Nat.lt_succ_of_lt hm)
    let z' := nConnectedCoverBasepoint (n + 2) (TopCat.of Z) z
    let p := nConnectedCoverProj (n + 2) (TopCat.of Z) z
    have hpz' : p.hom z' = z := nConnectedCoverProj_nConnectedCoverBasepoint (n + 2) (TopCat.of Z) z
    have hq'z' : (q.comp p.hom) z' = y := (congrArg q hpz').trans hqz
    have hπZ : Module.IsTorsion' (Additive (π_ (n + 2) Z z)) S :=
      (MulEquiv.ofBijective (HomotopyGroup.mapHom (N := Fin (n + 2)) q hqz)
        (hZbij (n + 2) le_rfl)).toAdditive.isTorsion'_iff.2 (hπ n (Nat.lt_succ_self n))
    refine ⟨nConnectedCover (n + 2) (TopCat.of Z) z, inferInstance, inferInstance,
      pathConnectedSpace_nConnectedCover (n + 2) (TopCat.of Z) z, z', q.comp p.hom, hq'z',
      fun k hk ↦ subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2)
        (TopCat.of Z) z z' (Nat.lt_succ_iff.1 hk),
      fun k hk ↦ ?_, fun k ↦ ?_⟩
    · rw [(HomotopyGroup.map_comp_map q hqz p.hom hpz').symm]
      exact (hZbij k (Nat.le_of_succ_le hk)).comp
        (bijective_homotopyGroupMap_nConnectedCoverProj (n + 2) (TopCat.of Z) z z' hpz'
          (Nat.lt_of_succ_le hk))
    · have h1 :=
        isIso_singularHomologyMap_nConnectedCoverProj z n (fun k _ hk ↦ hZconn k hk) hπZ A k
      have h2 := hZiso k
      rw [singularHomologyFunctor_obj_map] at h1
      rw [TopCat.ofHom_comp, TopCat.ofHom_hom, Functor.map_comp,
        HomologicalComplex.homologyMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end TauCeti

/-! ### Serre's Hurewicz isomorphism modulo `S`-torsion -/

namespace HomotopyGroup

open TauCeti

section Localization

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
  {S : Submonoid ℤ} {n : ℕ}

/-- **Hurewicz isomorphism modulo `S`-torsion (bijectivity of base change).** Let `Y` be a simply
connected space whose homotopy groups `π_{m + 2}(Y, y)` are `S`-torsion for all `m < n`, and let
`A` be a localization of `ℤ` at `S`. Then the base-changed Hurewicz homomorphism
`A ⊗[ℤ] Additive (π_{n + 2}(Y, y)) → A ⊗[ℤ] H_{n + 2}(Y; ℤ)` is bijective. -/
theorem bijective_hurewiczIntLinearMap_baseChange
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    Function.Bijective ((hurewiczIntLinearMap Y y n).baseChange A) := by
  have : @Module.Flat ℤ A _ _ Algebra.toModule := IsLocalization.flat A S
  obtain ⟨Z, _, _, _, z, q, hqz, hZconn, hZbij, hZiso⟩ :=
    exists_connected_cover_of_isTorsion' y S A n hπ
  have hnat := congrArg (LinearMap.baseChange A)
    (singularHomologyMap_comp_hurewiczIntLinearMap q hqz n)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hnat
  have hqH := (bijective_singularHomologyMap_baseChange_iff_isIso ℤ A (TopCat.ofHom q) (n + 2)).2
    (hZiso (n + 2))
  have hZhur : Function.Bijective (hurewiczIntLinearMap Z z n) := by
    have hfun : ⇑(hurewiczIntLinearMap Z z n) =
        (fun a ↦ (hurewicz (ModuleCat.of ℤ ℤ) (n + 1) a).hom 1) ∘ Additive.toMul :=
      funext fun a ↦ (hurewiczIntLinearMap_apply Z z n a).trans (hurewiczIntHom_apply Z z (n + 1) a)
    rw [hfun]
    exact (bijective_hurewicz hZconn).comp Additive.toMul.bijective
  have hqπ : Function.Bijective
      ((HomotopyGroup.mapHom (N := Fin (n + 2)) q hqz).toAdditive.toIntLinearMap) :=
    Additive.ofMul.bijective.comp ((hZbij (n + 2) le_rfl).comp Additive.toMul.bijective)
  have hlhs : Function.Bijective
      (((hurewiczIntLinearMap Y y n).baseChange A).comp
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) q hqz).toAdditive.toIntLinearMap.baseChange A)) :=
    hnat ▸ hqH.comp (LinearMap.bijective_baseChange_of_bijective hZhur)
  exact (Function.Bijective.of_comp_iff _ (LinearMap.bijective_baseChange_of_bijective hqπ)).1 hlhs

/-- Localized Hurewicz equivalence using the `Algebra.toModule` `ℤ`-module structure on `A`. -/
private def hurewiczLocalizationLinearEquivAux
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    (@TensorProduct ℤ _ A (Additive (HomotopyGroup (Fin (n + 2)) Y y)) _ _ Algebra.toModule _)
        ≃ₗ[A]
      ((singularChains A).obj (TopCat.of Y)).homology (n + 2) :=
  have : @Module.Flat ℤ A _ _ Algebra.toModule := IsLocalization.flat A S
  (LinearEquiv.ofBijective ((hurewiczIntLinearMap Y y n).baseChange A)
      (bijective_hurewiczIntLinearMap_baseChange hπ A)).trans
    (singularHomologyTensorIso ℤ A (TopCat.of Y) (n + 2)).toLinearEquiv

/-- **Hurewicz isomorphism modulo `S`-torsion.** Under the hypotheses of
`HomotopyGroup.bijective_hurewiczIntLinearMap_baseChange`, base change of the integral Hurewicz
homomorphism composed with `TauCeti.singularHomologyTensorIso` yields an `A`-linear isomorphism
`A ⊗[ℤ] Additive (π_{n + 2}(Y, y)) ≃ₗ[A] H_{n + 2}(Y; A)`. -/
def hurewiczLocalizationLinearEquiv
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    A ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) Y y) ≃ₗ[A]
      ((singularChains A).obj (TopCat.of Y)).homology (n + 2) :=
  (TensorProduct.congrIntModule A _ (AddCommGroup.toIntModule A) Algebra.toModule).trans
    (hurewiczLocalizationLinearEquivAux hπ A)

@[simp]
theorem hurewiczLocalizationLinearEquiv_tmul
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A]
    (a : A) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczLocalizationLinearEquiv hπ A (a ⊗ₜ[ℤ] x) =
      (have : @Module.Flat ℤ A _ _ Algebra.toModule := IsLocalization.flat A S
       (singularHomologyTensorIso ℤ A (TopCat.of Y) (n + 2)).hom.hom
         (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a
           (hurewiczIntLinearMap Y y n x))) := by
  have : @Module.Flat ℤ A _ _ Algebra.toModule := IsLocalization.flat A S
  rw [hurewiczLocalizationLinearEquiv, LinearEquiv.trans_apply, TensorProduct.congrIntModule_tmul,
    hurewiczLocalizationLinearEquivAux, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    LinearMap.baseChange_tmul, Iso.toLinearEquiv_apply]

/-- **Naturality of the localized Hurewicz isomorphism** with respect to based continuous maps. -/
theorem singularHomologyMap_hurewiczLocalizationLinearEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} [Subsingleton (π_ 1 X x)] [Subsingleton (π_ 1 Y y)]
    {S : Submonoid ℤ} {n : ℕ}
    (hπX : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) X x)) S)
    (hπY : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A]
    (f : C(X, Y)) (hf : f x = y)
    (z : A ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (HomologicalComplex.homologyMap ((singularChains A).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczLocalizationLinearEquiv hπX A z) =
      hurewiczLocalizationLinearEquiv hπY A
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.lTensor A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a γ =>
    have : @Module.Flat ℤ A _ _ Algebra.toModule := IsLocalization.flat A S
    rw [LinearMap.lTensor_tmul, hurewiczLocalizationLinearEquiv_tmul,
      hurewiczLocalizationLinearEquiv_tmul]
    have hnat := singularHomologyTensorIso_hom_naturality ℤ A (TopCat.ofHom f) (n + 2)
    have hnat_apply := congrArg (fun g ↦ g.hom
      (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a
        (hurewiczIntLinearMap X x n γ))) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.baseChange_tmul] at hnat_apply
    rw [← hnat_apply]
    congr 2
    exact congrArg (fun g ↦ g γ) (singularHomologyMap_comp_hurewiczIntLinearMap f hf n)
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

/-- **The kernel of the integral Hurewicz homomorphism is `S`-torsion** when `Y` is simply connected
and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`. -/
theorem isTorsion'_ker_hurewiczIntLinearMap
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) :
    Module.IsTorsion' (LinearMap.ker (hurewiczIntLinearMap Y y n)) S :=
  have : IsLocalization S (Localization S) := Localization.isLocalization
  (((hurewiczIntLinearMap Y y n).bijective_baseChange_iff S (Localization S)).1
    (bijective_hurewiczIntLinearMap_baseChange hπ (Localization S))).1

/-- **The cokernel of the integral Hurewicz homomorphism is `S`-torsion** when `Y` is simply
connected and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`. -/
theorem isTorsion'_quotient_range_hurewiczIntLinearMap
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) :
    Module.IsTorsion'
      ((((singularChains ℤ).obj (TopCat.of Y)).homology (n + 2)) ⧸
        LinearMap.range (hurewiczIntLinearMap Y y n)) S := by
  have : IsLocalization S (Localization S) := Localization.isLocalization
  convert (((hurewiczIntLinearMap Y y n).bijective_baseChange_iff S (Localization S)).1
    (bijective_hurewiczIntLinearMap_baseChange hπ (Localization S))).2
  exact congrArg (fun m : Module ℤ _ ↦ m.toSMul)
    (Subsingleton.elim (AddCommGroup.toIntModule _) (Submodule.Quotient.module _))

end Localization

end HomotopyGroup

/-! ### Serre's connectivity equivalence modulo `S`-torsion -/

namespace TauCeti

section ConnectivityEquivalence

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)]

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`, then
`H_{m + 2}(Y; A) = 0` for every localization `A` of `ℤ` at `S` and all `m < n`. -/
theorem subsingleton_singularHomology_of_forall_isTorsion'_homotopyGroup
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] {n : ℕ}
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    {m : ℕ} (hm : m < n) :
    Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := by
  obtain ⟨Z, _, _, _, z, q, _, hZconn, _, hZiso⟩ :=
    exists_connected_cover_of_isTorsion' y S A n hπ
  have : Subsingleton (((singularChains A).obj (TopCat.of Z)).homology (m + 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup hZconn A
        (Nat.succ_ne_zero _) (by omega))
  have := hZiso (m + 2)
  exact (asIso (HomologicalComplex.homologyMap ((singularChains A).map (TopCat.ofHom q))
    (m + 2))).toLinearEquiv.toEquiv.symm.subsingleton

/-- **Serre's connectivity equivalence modulo `S`-torsion (localized homology form).** For a
simply connected space `(Y, y)`, a submonoid `S : Submonoid ℤ`, a localization `A` of `ℤ` at `S`,
and any `n : ℕ`, the homotopy groups `π_{m + 2}(Y, y)` are `S`-torsion for all `m < n` if and
only if `H_{m + 2}(Y; A) = 0` for all `m < n`. -/
theorem forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] (n : ℕ) :
    (∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m < n, Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := by
  refine ⟨fun hπ m hm ↦
    subsingleton_singularHomology_of_forall_isTorsion'_homotopyGroup y S A hπ hm, fun hH m hm ↦ ?_⟩
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have : Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := hH m hm
    exact (S.isTorsion'_iff_subsingleton_tensorProduct A).2
      (HomotopyGroup.hurewiczLocalizationLinearEquivAux
        (fun j hj ↦ ih j hj (lt_trans hj hm)) A).toEquiv.subsingleton

/-- **Serre's connectivity equivalence modulo `S`-torsion (integral homology form, Serre 1953
Theorem 1).** For a simply connected space `(Y, y)`, a submonoid `S : Submonoid ℤ`, and any
`n : ℕ`, `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n` if and only if `H_{m + 2}(Y; ℤ)` is
`S`-torsion for all `m < n`. -/
theorem forall_isTorsion'_homotopyGroup_iff_singularHomology (S : Submonoid ℤ) (n : ℕ) :
    (∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m < n,
        Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) S := by
  have : IsLocalization S (Localization S) := Localization.isLocalization
  rw [forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S (Localization S) n]
  exact forall_congr' fun m ↦ imp_congr_right fun _ ↦
    (isTorsion'_singularChains_int_homology_iff S (Localization S) (TopCat.of Y) (m + 2)).symm

/-- **All-degrees connectivity equivalence modulo `S`-torsion**: all higher homotopy groups
`π_{m + 2}(Y, y)` of a simply connected space `Y` are `S`-torsion if and only if all higher
integral homology groups `H_{m + 2}(Y; ℤ)` are `S`-torsion. -/
theorem forall_isTorsion'_homotopyGroup_iff_forall_singularHomology (S : Submonoid ℤ) :
    (∀ m : ℕ, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m : ℕ, Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) S :=
  ⟨fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_singularHomology y S (m + 1)).1
    (fun j _ ↦ h j) m (Nat.lt_succ_self m),
   fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_singularHomology y S (m + 1)).2
    (fun j _ ↦ h j) m (Nat.lt_succ_self m)⟩

/-- **All-degrees connectivity equivalence modulo `S`-torsion (localized form)**: all higher
homotopy groups `π_{m + 2}(Y, y)` of a simply connected space `Y` are `S`-torsion if and only if
`H_{m + 2}(Y; A) = 0` for all `m : ℕ`. -/
theorem forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    (∀ m : ℕ, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m : ℕ, Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) :=
  ⟨fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S A (m + 1)).1
    (fun j _ ↦ h j) m (Nat.lt_succ_self m),
   fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S A (m + 1)).2
    (fun j _ ↦ h j) m (Nat.lt_succ_self m)⟩

end ConnectivityEquivalence

end TauCeti

/-! ### Rational Hurewicz theorem -/

namespace HomotopyGroup

open TauCeti

section Rational

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
  {n : ℕ}

/-- **The rational Hurewicz theorem** (homotopy-group hypothesis). If `Y` is simply connected and
`π_{m + 2}(Y, y)` is torsion for all `m < n`, then the rationalized Hurewicz map is a `ℚ`-linear
isomorphism `ℚ ⊗[ℤ] Additive (π_{n + 2}(Y, y)) ≃ₗ[ℚ] H_{n + 2}(Y; ℚ)`. -/
def hurewiczRatLinearEquiv
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) Y y) ≃ₗ[ℚ]
      ((singularChains ℚ).obj (TopCat.of Y)).homology (n + 2) :=
  hurewiczLocalizationLinearEquiv (S := nonZeroDivisors ℤ)
    (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm)) ℚ

@[simp]
theorem hurewiczRatLinearEquiv_tmul
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y)))
    (a : ℚ) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczRatLinearEquiv hπ (a ⊗ₜ[ℤ] x) =
      (have : @Module.Flat ℤ ℚ _ _ Algebra.toModule := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
       (singularHomologyTensorIso ℤ ℚ (TopCat.of Y) (n + 2)).hom.hom
         (@TensorProduct.tmul ℤ _ ℚ _ _ _ Algebra.toModule _ a (hurewiczIntLinearMap Y y n x))) :=
  hurewiczLocalizationLinearEquiv_tmul _ ℚ a x

/-- **Naturality of `HomotopyGroup.hurewiczRatLinearEquiv`** with respect to based continuous
maps. -/
theorem singularHomologyMap_hurewiczRatLinearEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} [Subsingleton (π_ 1 X x)] [Subsingleton (π_ 1 Y y)]
    {n : ℕ}
    (hπX : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) X x)))
    (hπY : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y)))
    (f : C(X, Y)) (hf : f x = y)
    (z : ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (HomologicalComplex.homologyMap ((singularChains ℚ).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczRatLinearEquiv hπX z) =
      hurewiczRatLinearEquiv hπY
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.lTensor ℚ z) :=
  singularHomologyMap_hurewiczLocalizationLinearEquiv _ _ ℚ f hf z

/-- **The rational Hurewicz theorem** (rational homology hypothesis). If `Y` is simply connected
and `H_{m + 2}(Y; ℚ) = 0` for all `m < n`, then
`ℚ ⊗[ℤ] Additive (π_{n + 2}(Y, y)) ≃ₗ[ℚ] H_{n + 2}(Y; ℚ)`. -/
def hurewiczRatLinearEquivOfSubsingleton
    (hH : ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2))) :
    ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) Y y) ≃ₗ[ℚ]
      ((singularChains ℚ).obj (TopCat.of Y)).homology (n + 2) :=
  hurewiczLocalizationLinearEquiv (S := nonZeroDivisors ℤ)
    ((forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y (nonZeroDivisors ℤ) ℚ
      n).2 hH) ℚ

@[simp]
theorem hurewiczRatLinearEquivOfSubsingleton_tmul
    (hH : ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)))
    (a : ℚ) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczRatLinearEquivOfSubsingleton hH (a ⊗ₜ[ℤ] x) =
      (have : @Module.Flat ℤ ℚ _ _ Algebra.toModule := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
       (singularHomologyTensorIso ℤ ℚ (TopCat.of Y) (n + 2)).hom.hom
         (@TensorProduct.tmul ℤ _ ℚ _ _ _ Algebra.toModule _ a (hurewiczIntLinearMap Y y n x))) :=
  hurewiczLocalizationLinearEquiv_tmul _ ℚ a x

/-- **Naturality of `HomotopyGroup.hurewiczRatLinearEquivOfSubsingleton`** with respect to based
continuous maps. -/
theorem singularHomologyMap_hurewiczRatLinearEquivOfSubsingleton
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} [Subsingleton (π_ 1 X x)] [Subsingleton (π_ 1 Y y)]
    {n : ℕ}
    (hHX : ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of X)).homology (m + 2)))
    (hHY : ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)))
    (f : C(X, Y)) (hf : f x = y)
    (z : ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (HomologicalComplex.homologyMap ((singularChains ℚ).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczRatLinearEquivOfSubsingleton hHX z) =
      hurewiczRatLinearEquivOfSubsingleton hHY
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.lTensor ℚ z) :=
  singularHomologyMap_hurewiczLocalizationLinearEquiv _ _ ℚ f hf z

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is torsion for all `m < n`, then the kernel
of the integral Hurewicz map in degree `n + 2` is torsion. -/
theorem isAddTorsion_ker_hurewiczIntLinearMap
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    IsAddTorsion (LinearMap.ker (hurewiczIntLinearMap Y y n)) :=
  isAddTorsion_iff_isTorsion_int.2 <|
    isTorsion'_ker_hurewiczIntLinearMap (S := nonZeroDivisors ℤ)
      (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm))

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is torsion for all `m < n`, then the cokernel
of the integral Hurewicz map in degree `n + 2` is torsion. -/
theorem isAddTorsion_quotient_range_hurewiczIntLinearMap
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    IsAddTorsion
      ((((singularChains ℤ).obj (TopCat.of Y)).homology (n + 2)) ⧸
        LinearMap.range (hurewiczIntLinearMap Y y n)) :=
  isAddTorsion_iff_isTorsion_int.2 <|
    isTorsion'_quotient_range_hurewiczIntLinearMap (S := nonZeroDivisors ℤ)
      (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm))

end Rational

end HomotopyGroup

namespace TauCeti

section RationalConnectivity

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)]

/-- **Rational connectivity equivalence (rational homology form).** For a simply connected space
`(Y, y)`, `π_{m + 2}(Y, y)` is torsion for all `m < n` if and only if `H_{m + 2}(Y; ℚ) = 0` for
all `m < n`. -/
theorem forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat (n : ℕ) :
    (∀ m < n, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)) := by
  simp only [isAddTorsion_iff_isTorsion_int]
  exact
    forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y (nonZeroDivisors ℤ) ℚ n

/-- **Rational connectivity equivalence (integral homology form).** For a simply connected space
`(Y, y)`, `π_{m + 2}(Y, y)` is torsion for all `m < n` if and only if `H_{m + 2}(Y; ℤ)` is
torsion for all `m < n`. -/
theorem forall_isAddTorsion_homotopyGroup_iff_singularHomology (n : ℕ) :
    (∀ m < n, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m < n, IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) := by
  rw [forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat y n]
  exact forall_congr' fun m ↦ imp_congr_right fun _ ↦
    (isAddTorsion_singularChains_homology_iff (TopCat.of Y) (m + 2)).symm

/-- A simply connected space `Y` has all higher homotopy groups torsion if and only if its
positive-degree rational homology vanishes. -/
theorem forall_isAddTorsion_homotopyGroup_iff_forall_subsingleton_rat :
    (∀ m : ℕ, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m : ℕ, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)) := by
  simp only [isAddTorsion_iff_isTorsion_int]
  exact forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology y
    (nonZeroDivisors ℤ) ℚ

end RationalConnectivity

end TauCeti

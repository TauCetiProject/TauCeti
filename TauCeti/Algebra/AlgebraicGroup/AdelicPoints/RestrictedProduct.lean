/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdelicPoints.IntegralModel
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Adelic points of affine group schemes as restricted products

Let `F` be a number field, `H` a commutative Hopf `F`-algebra representing an affine group scheme
`G = Spec H`, and `M : IntegralModel F H S` an integral model of `G` away from a finite set `S` of
height-one primes of `𝓞 F`.

This file establishes the topological group isomorphism between the finite adelic points
`FiniteAdelicPoints F H = G(𝔸_{F,f})` (equipped with the point topology) and the restricted product
`Πʳ v, [LocalPoints F H v, M.level v]` of local points `G(F_v)` with respect to the compact open
reference subgroups `M.level v`:

* **Restricted-product homomorphism**: coordinate projections
  `finiteLocalProjection v : G(𝔸_{F,f}) →* G(F_v)` land in `M.level v` at all but finitely many
  places (`eventually_finiteLocalProjection_mem_level`) and assemble into a continuous group
  homomorphism `M.toRestrictedProductMonoidHom`.
* **Restricted-product isomorphism**: `M.restrictedProductEquiv` upgrades
  `M.toRestrictedProductMonoidHom` to a topological group isomorphism
  `FiniteAdelicPoints F H ≃ₜ* Πʳ v, [LocalPoints F H v, M.level v]` whose inverse evaluates each
  coordinate `h ∈ H` place-by-place in `𝔸_{F,f}`, yielding the packaged comparison theorem
  `M.exists_restrictedProductEquiv`.
* **Full adelic decomposition**: combining `AdelicPoints.prodEquiv` with
  `M.restrictedProductEquiv` identifies `G(𝔸_F)` as a topological group with
  `G(F_∞) × Πʳ v, [G(F_v), M.level v]` (`M.adelicRestrictedProductEquiv`).
* **Independence of the integral model**: for any two integral models `M₁` (away from `S₁`) and `M₂`
  (away from `S₂`) of `(F, H)`, their level families `M₁.level` and `M₂.level` agree at all but
  finitely many places (`eventually_level_eq`), inducing a canonical coordinatewise-identity
  topological group isomorphism `M₁.levelChangeEquiv M₂` compatible with `restrictedProductEquiv`.

## Main declarations

* `TauCeti.IntegralModel.toRestrictedProductMonoidHom`,
  `TauCeti.IntegralModel.continuous_toRestrictedProductMonoidHom`: the continuous coordinatewise
  group homomorphism `FiniteAdelicPoints F H →* Πʳ v, [LocalPoints F H v, M.level v]`.
* `TauCeti.IntegralModel.restrictedProductEquiv`: topological group isomorphism
  `FiniteAdelicPoints F H ≃ₜ* Πʳ v, [LocalPoints F H v, M.level v]`.
* `TauCeti.IntegralModel.exists_restrictedProductEquiv`: packaged existence and coordinate formula
  for the restricted-product comparison.
* `TauCeti.IntegralModel.adelicRestrictedProductEquiv`: full adelic decomposition
  `AdelicPoints F H ≃ₜ* InfinitePoints F H × Πʳ v, [LocalPoints F H v, M.level v]`.
* `TauCeti.IntegralModel.eventually_level_eq`, `TauCeti.IntegralModel.levelChangeEquiv`,
  `TauCeti.IntegralModel.restrictedProductEquiv_trans_levelChangeEquiv`: independence of the choice
  of integral model.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Rem. 3.5 and Thm. 3.6, pp. 5–6.
* J. S. Milne, *Adelic Algebraic Groups*, §4, pp. 42–43.
-/

public section

open CategoryTheory Filter IsDedekindDomain NumberField TensorProduct Topology WithConv
open scoped RestrictedProduct
open TauCeti.AdelicPoints TauCeti.PointTopology

namespace TauCeti.IntegralModel

universe u

variable {F : Type u} [Field F] [NumberField F] {H : Type u} [CommRing H] [HopfAlgebra F H]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

/-! ### Forward homomorphism into the restricted product and its continuity -/

/-- For any finite adelic point `x ∈ G(𝔸_{F,f})`, its local projection at `v` lies in `M.level v`
for all but finitely many height-one primes `v`. -/
theorem eventually_finiteLocalProjection_mem_level (M : IntegralModel F H S)
    (x : FiniteAdelicPoints F H) :
    ∀ᶠ v in cofinite, finiteLocalProjection v x ∈ M.level v := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := SIntegers F S) (A := M.coordinate)
  let a : s → M.coordinate := Subtype.val
  have ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤ := by simpa [a] using hs
  have hgen : ∀ᶠ v in cofinite,
      ∀ i : s, (x.ofConv (M.toBase (a i))) v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr fun i ↦ (x.ofConv (M.toBase (a i))).cofinite_mem_adicCompletionIntegers
  filter_upwards [S.finite_toSet.compl_mem_cofinite, hgen] with v hv hi
  rw [M.level_of_notMem hv, M.mem_localPoints_iff_of_adjoin_eq_top v hv ha]
  intro i
  simpa only [finiteLocalProjection_ofConv_apply, M.toBase_apply] using hi i

/-- The coordinatewise group homomorphism `G(𝔸_{F,f}) →* Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def toRestrictedProductMonoidHom (M : IntegralModel F H S) :
    FiniteAdelicPoints F H →* Πʳ v, [LocalPoints F H v, M.level v] where
  toFun x := ⟨fun v ↦ finiteLocalProjection v x, M.eventually_finiteLocalProjection_mem_level x⟩
  map_one' := DFunLike.coe_injective <| funext fun v ↦
    map_one (finiteLocalProjection (F := F) (H := H) v)
  map_mul' x y := DFunLike.coe_injective <| funext fun v ↦
    map_mul (finiteLocalProjection (F := F) (H := H) v) x y

@[simp]
theorem toRestrictedProductMonoidHom_apply (M : IntegralModel F H S)
    (x : FiniteAdelicPoints F H) (v : HeightOneSpectrum (𝓞 F)) :
    M.toRestrictedProductMonoidHom x v = finiteLocalProjection v x := by
  rw [toRestrictedProductMonoidHom]
  rfl

/-- The coordinatewise homomorphism `M.toRestrictedProductMonoidHom` from finite adelic points to
the restricted product of local points is continuous. -/
@[continuity, fun_prop]
theorem continuous_toRestrictedProductMonoidHom (M : IntegralModel F H S) :
    Continuous M.toRestrictedProductMonoidHom := by
  refine continuous_of_continuousAt_one M.toRestrictedProductMonoidHom ?_
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := SIntegers F S) (A := M.coordinate)
  let a : s → M.coordinate := Subtype.val
  have ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤ := by simpa [a] using hs
  let U : Set (FiniteAdelicPoints F H) :=
    ⋂ i : s, (fun x : FiniteAdelicPoints F H ↦ x.ofConv (M.toBase (a i))) ⁻¹'
      (FiniteAdeleRing.sIntegralAdeles (𝓞 F) F (S : Set _) : Set (FiniteAdeleRing (𝓞 F) F))
  have hU_open : IsOpen U :=
    isOpen_iInter_of_finite fun i ↦
      (FiniteAdeleRing.isOpen_sIntegralAdeles (𝓞 F) F (S : Set _)).preimage
        (continuous_eval_ofConv _)
  have h1U : (1 : FiniteAdelicPoints F H) ∈ U := by
    refine Set.mem_iInter.mpr fun i ↦ FiniteAdeleRing.mem_sIntegralAdeles.mpr fun v hv ↦ ?_
    have h1loc : finiteLocalProjection v (1 : FiniteAdelicPoints F H) ∈ M.localPoints v hv := by
      rw [map_one]
      exact one_mem _
    simpa only [finiteLocalProjection_ofConv_apply, M.toBase_apply] using
      (M.mem_localPoints_iff v hv).mp h1loc (a i)
  have hU_mem (u : U) (v : HeightOneSpectrum (𝓞 F)) :
      M.toRestrictedProductMonoidHom u.1 v ∈ M.level v := by
    by_cases hv : v ∈ S
    · rw [M.level_of_mem hv]
      exact Subgroup.mem_top _
    · rw [M.level_of_notMem hv, M.toRestrictedProductMonoidHom_apply,
        M.mem_localPoints_iff_of_adjoin_eq_top v hv ha]
      intro i
      have hu := Set.mem_iInter.mp u.2 i
      have hv_int := FiniteAdeleRing.mem_sIntegralAdeles.mp hu v hv
      simpa only [finiteLocalProjection_ofConv_apply, M.toBase_apply] using hv_int
  have hU_cont : Continuous (fun u : U ↦ M.toRestrictedProductMonoidHom u.1) := by
    rw [TauCeti.continuous_restrictedProduct_iff_of_forall_mem (T := Set.univ)
      (le_principal_iff.mpr univ_mem) (fun u v _ ↦ hU_mem u v)]
    exact continuous_pi fun v ↦ (continuous_finiteLocalProjection v).comp continuous_subtype_val
  exact (continuousOn_iff_continuous_domRestrict.mpr hU_cont).continuousAt (hU_open.mem_nhds h1U)

/-! ### Inverse map from the restricted product and its continuity -/

private theorem exists_continuous_adele_eval_baseChange (M : IntegralModel F H S)
    (t : F ⊗[SIntegers F S] M.coordinate) :
    ∃ φ : (Πʳ v, [LocalPoints F H v, M.level v]) → FiniteAdeleRing (𝓞 F) F,
      Continuous φ ∧ ∀ y v, φ y v = (y v).ofConv (M.baseChangeIso.hom.hom t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    have hmaps : ∀ᶠ v in cofinite,
        Set.MapsTo (fun g : LocalPoints F H v ↦ g.ofConv (M.toBase a))
          (M.level v : Set (LocalPoints F H v))
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv g hg
      rw [SetLike.mem_coe, M.level_of_notMem hv, M.mem_localPoints_iff] at hg
      simpa only [SetLike.mem_coe, M.toBase_apply] using hg a
    let φ₀ : (Πʳ v, [LocalPoints F H v, M.level v]) → FiniteAdeleRing (𝓞 F) F :=
      RestrictedProduct.mapAlong
        (fun v : HeightOneSpectrum (𝓞 F) ↦ LocalPoints F H v)
        (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
        (A₁ := fun v ↦ (M.level v : Set (LocalPoints F H v)))
        (A₂ := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        id tendsto_id (fun _ g ↦ g.ofConv (M.toBase a)) hmaps
    have hφ₀_cont : Continuous φ₀ :=
      RestrictedProduct.mapAlong_continuous
        (fun v : HeightOneSpectrum (𝓞 F) ↦ LocalPoints F H v)
        (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
        (A₁ := fun v ↦ (M.level v : Set (LocalPoints F H v)))
        (A₂ := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        id tendsto_id (fun _ g ↦ g.ofConv (M.toBase a)) hmaps
        (fun _ ↦ continuous_eval_ofConv (M.toBase a))
    refine ⟨fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) c * φ₀ y,
      continuous_const.mul hφ₀_cont, fun y v ↦ ?_⟩
    have htmul : M.baseChangeIso.hom.hom (c ⊗ₜ[SIntegers F S] a) = c • M.toBase a := by
      have hc : c ⊗ₜ[SIntegers F S] a = c • ((1 : F) ⊗ₜ[SIntegers F S] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, M.toBase_apply]
    rw [htmul, map_smul, Algebra.smul_def, FiniteAdeleRing.mul_apply,
      FiniteAdeleRing.algebraMap_apply]
    rfl
  | add t₁ t₂ ih₁ ih₂ =>
    obtain ⟨φ₁, hcont₁, hφ₁⟩ := ih₁
    obtain ⟨φ₂, hcont₂, hφ₂⟩ := ih₂
    refine ⟨fun y ↦ φ₁ y + φ₂ y, hcont₁.add hcont₂, fun y v ↦ ?_⟩
    rw [FiniteAdeleRing.add_apply, hφ₁, hφ₂, ← map_add, ← map_add]

private theorem exists_continuous_adele_eval (M : IntegralModel F H S) (h : H) :
    ∃ φ : (Πʳ v, [LocalPoints F H v, M.level v]) → FiniteAdeleRing (𝓞 F) F,
      Continuous φ ∧ ∀ y v, φ y v = (y v).ofConv h := by
  obtain ⟨φ, hcont, hφ⟩ := exists_continuous_adele_eval_baseChange M (M.baseChangeIso.inv.hom h)
  refine ⟨φ, hcont, fun y v ↦ ?_⟩
  rw [hφ, M.baseChangeIso.inv_hom_id_apply h]

private noncomputable def adeleEval (M : IntegralModel F H S) (h : H) :
    (Πʳ v, [LocalPoints F H v, M.level v]) → FiniteAdeleRing (𝓞 F) F :=
  Classical.choose (exists_continuous_adele_eval M h)

private theorem continuous_adeleEval (M : IntegralModel F H S) (h : H) :
    Continuous (adeleEval M h) :=
  (Classical.choose_spec (exists_continuous_adele_eval M h)).1

private theorem adeleEval_apply (M : IntegralModel F H S) (h : H)
    (y : Πʳ v, [LocalPoints F H v, M.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    adeleEval M h y v = (y v).ofConv h :=
  (Classical.choose_spec (exists_continuous_adele_eval M h)).2 y v

private noncomputable def fromRestrictedProductFun (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints F H v, M.level v]) : FiniteAdelicPoints F H :=
  toConv
    { toFun h := adeleEval M h y
      map_one' := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_one, FiniteAdeleRing.one_apply]
      map_mul' h₁ h₂ := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_mul, FiniteAdeleRing.mul_apply,
          adeleEval_apply, adeleEval_apply]
      map_zero' := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_zero, FiniteAdeleRing.zero_apply]
      map_add' h₁ h₂ := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, map_add, FiniteAdeleRing.add_apply,
          adeleEval_apply, adeleEval_apply]
      commutes' c := FiniteAdeleRing.ext F fun v ↦ by
        rw [adeleEval_apply, AlgHom.commutes, FiniteAdeleRing.algebraMap_apply]
        rfl }

private theorem fromRestrictedProductFun_ofConv_apply (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints F H v, M.level v]) (h : H) (v : HeightOneSpectrum (𝓞 F)) :
    ((fromRestrictedProductFun M y).ofConv h) v = (y v).ofConv h :=
  adeleEval_apply M h y v

private theorem continuous_fromRestrictedProductFun (M : IntegralModel F H S) :
    Continuous (fromRestrictedProductFun M) :=
  continuous_withConv_iff.mpr fun h ↦ continuous_adeleEval M h

/-! ### Packaged restricted-product equivalence -/

/-- **Adelic points as a restricted product**: for an integral model `M` of `G = Spec H` away from
`S`, coordinate projections induce a topological group isomorphism between `G(𝔸_{F,f})` and the
restricted product `Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def restrictedProductEquiv (M : IntegralModel F H S) :
    FiniteAdelicPoints F H ≃ₜ* Πʳ v, [LocalPoints F H v, M.level v] where
  toFun := M.toRestrictedProductMonoidHom
  invFun := fromRestrictedProductFun M
  left_inv x := ofConv_injective <| AlgHom.ext fun h ↦ FiniteAdeleRing.ext F fun v ↦ by
    rw [fromRestrictedProductFun_ofConv_apply, M.toRestrictedProductMonoidHom_apply,
      finiteLocalProjection_ofConv_apply]
  right_inv y := DFunLike.coe_injective <| funext fun v ↦
    ofConv_injective <| AlgHom.ext fun h ↦ by
      rw [M.toRestrictedProductMonoidHom_apply, finiteLocalProjection_ofConv_apply,
        fromRestrictedProductFun_ofConv_apply]
  map_mul' := map_mul M.toRestrictedProductMonoidHom
  continuous_toFun := M.continuous_toRestrictedProductMonoidHom
  continuous_invFun := continuous_fromRestrictedProductFun M

@[simp]
theorem coe_restrictedProductEquiv (M : IntegralModel F H S) :
    (M.restrictedProductEquiv :
      FiniteAdelicPoints F H →* Πʳ v, [LocalPoints F H v, M.level v]) =
      M.toRestrictedProductMonoidHom := by
  rw [restrictedProductEquiv]
  rfl

@[simp]
theorem restrictedProductEquiv_apply (M : IntegralModel F H S)
    (x : FiniteAdelicPoints F H) (v : HeightOneSpectrum (𝓞 F)) :
    M.restrictedProductEquiv x v = finiteLocalProjection v x := by
  rw [restrictedProductEquiv]
  rfl

theorem restrictedProductEquiv_apply_ofConv (M : IntegralModel F H S)
    (x : FiniteAdelicPoints F H) (v : HeightOneSpectrum (𝓞 F)) (h : H) :
    (M.restrictedProductEquiv x v).ofConv h = (x.ofConv h) v := by
  rw [M.restrictedProductEquiv_apply, finiteLocalProjection_ofConv_apply]

@[simp]
theorem restrictedProductEquiv_symm_ofConv_apply (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints F H v, M.level v]) (h : H) (v : HeightOneSpectrum (𝓞 F)) :
    ((M.restrictedProductEquiv.symm y).ofConv h) v = (y v).ofConv h := by
  rw [← M.restrictedProductEquiv_apply_ofConv, ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem finiteLocalProjection_restrictedProductEquiv_symm (M : IntegralModel F H S)
    (y : Πʳ v, [LocalPoints F H v, M.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    finiteLocalProjection v (M.restrictedProductEquiv.symm y) = y v := by
  rw [← M.restrictedProductEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

theorem restrictedProductEquiv_finiteDiagonal (M : IntegralModel F H S)
    (g : WithConv (H →ₐ[F] F)) (v : HeightOneSpectrum (𝓞 F)) :
    M.restrictedProductEquiv (finiteDiagonal g) v = localDiagonal v g := by
  rw [M.restrictedProductEquiv_apply, finiteLocalProjection_finiteDiagonal]

/-- Characterization of `T`-integral rational points in terms of `M.restrictedProductEquiv`. -/
theorem mem_globalPoints_iff_restrictedProductEquiv (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ v ∉ T, M.restrictedProductEquiv (finiteDiagonal g) v ∈ M.level v := by
  simp only [M.restrictedProductEquiv_finiteDiagonal, M.mem_globalPoints_iff_forall_level hST,
    localProjection_diagonal]

/-- **Restricted-product comparison theorem** (Conrad, Theorem 3.6): for any integral model `M` of
`G = Spec H` away from `S`, there is a topological group isomorphism
`FiniteAdelicPoints F H ≃ₜ* Πʳ v, [LocalPoints F H v, M.level v]` acting coordinatewise on
evaluations. -/
theorem exists_restrictedProductEquiv (M : IntegralModel F H S) :
    ∃ e : FiniteAdelicPoints F H ≃ₜ* Πʳ v, [LocalPoints F H v, M.level v],
      ∀ (x : FiniteAdelicPoints F H) (v : HeightOneSpectrum (𝓞 F)) (h : H),
        (e x v).ofConv h = (x.ofConv h) v :=
  ⟨M.restrictedProductEquiv, M.restrictedProductEquiv_apply_ofConv⟩

/-- Full adelic restricted-product decomposition: `G(𝔸_F)` is canonically isomorphic as a
topological group to `G(F_∞) × Πʳ v, [G(F_v), M.level v]`. -/
noncomputable def adelicRestrictedProductEquiv (M : IntegralModel F H S) :
    AdelicPoints F H ≃ₜ*
      InfinitePoints F H × Πʳ v, [LocalPoints F H v, M.level v] where
  toMulEquiv := (prodEquiv F H).toMulEquiv.trans
    ((MulEquiv.refl (InfinitePoints F H)).prodCongr M.restrictedProductEquiv.toMulEquiv)
  continuous_toFun :=
    (continuous_id.prodMap M.restrictedProductEquiv.continuous).comp (prodEquiv F H).continuous
  continuous_invFun :=
    (prodEquiv F H).symm.continuous.comp
      (continuous_id.prodMap M.restrictedProductEquiv.symm.continuous)

@[simp]
theorem adelicRestrictedProductEquiv_fst (M : IntegralModel F H S) (x : AdelicPoints F H) :
    (M.adelicRestrictedProductEquiv x).1 = infiniteProjection x := by
  rw [adelicRestrictedProductEquiv]
  exact prodEquiv_fst x

@[simp]
theorem adelicRestrictedProductEquiv_snd_apply (M : IntegralModel F H S)
    (x : AdelicPoints F H) (v : HeightOneSpectrum (𝓞 F)) :
    (M.adelicRestrictedProductEquiv x).2 v = localProjection v x := by
  rw [adelicRestrictedProductEquiv]
  exact (M.restrictedProductEquiv_apply (prodEquiv F H x).2 v).trans <| by
    rw [prodEquiv_snd]
    exact ofConv_injective <| AlgHom.ext fun h ↦ by simp

/-! ### Independence of the integral model -/

section ModelIndependence

private theorem eventually_eval_baseChange_mem_integers (M : IntegralModel F H S)
    (t : F ⊗[SIntegers F S] M.coordinate) :
    ∀ᶠ v in cofinite, ∀ (hv : v ∉ S) {g : LocalPoints F H v},
      g ∈ M.localPoints v hv →
        g.ofConv (M.baseChangeIso.hom.hom t) ∈ v.adicCompletionIntegers F := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    filter_upwards [(algebraMap F (FiniteAdeleRing (𝓞 F) F) c).cofinite_mem_adicCompletionIntegers]
      with v hc hv g hg
    have htmul : M.baseChangeIso.hom.hom (c ⊗ₜ[SIntegers F S] a) =
        c • M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a) := by
      have hc' : c ⊗ₜ[SIntegers F S] a = c • ((1 : F) ⊗ₜ[SIntegers F S] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc', map_smul]
    rw [htmul, map_smul, Algebra.smul_def]
    exact mul_mem hc ((M.mem_localPoints_iff v hv).mp hg a)
  | add t₁ t₂ ih₁ ih₂ =>
    filter_upwards [ih₁, ih₂] with v hv₁ hv₂ hv g hg
    rw [map_add, map_add]
    exact add_mem (hv₁ hv hg) (hv₂ hv hg)

private theorem eventually_localPoints_le
    {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    ∀ᶠ v in cofinite, ∀ (hv₁ : v ∉ S₁) (hv₂ : v ∉ S₂),
      M₂.localPoints v hv₂ ≤ M₁.localPoints v hv₁ := by
  obtain ⟨s₁, hs₁⟩ := Algebra.FiniteType.out (R := SIntegers F S₁) (A := M₁.coordinate)
  let a : s₁ → M₁.coordinate := Subtype.val
  have ha : Algebra.adjoin (SIntegers F S₁) (Set.range a) = ⊤ := by simpa [a] using hs₁
  have hgen : ∀ᶠ v in cofinite, ∀ i : s₁, ∀ (hv₂ : v ∉ S₂) {g : LocalPoints F H v},
      g ∈ M₂.localPoints v hv₂ →
        g.ofConv (M₁.toBase (a i)) ∈ v.adicCompletionIntegers F := by
    refine eventually_all.mpr fun i ↦ ?_
    filter_upwards [eventually_eval_baseChange_mem_integers M₂
      (M₂.baseChangeIso.inv.hom (M₁.toBase (a i)))] with v hv hv₂ g hg
    simpa only [M₂.baseChangeIso.inv_hom_id_apply] using hv hv₂ hg
  filter_upwards [hgen] with v hv hv₁ hv₂ g hg
  rw [M₁.mem_localPoints_iff_of_adjoin_eq_top v hv₁ ha]
  intro i
  simpa only [M₁.toBase_apply] using hv i hv₂ hg

/-- **Model independence of local integral subgroups**: for any two integral models `M₁` and `M₂` of
the same affine group scheme `(F, H)`, their reference subgroups `M₁.level v` and `M₂.level v` agree
at all but finitely many height-one primes `v`. -/
theorem eventually_level_eq {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    ∀ᶠ v in cofinite, M₁.level v = M₂.level v := by
  filter_upwards [S₁.finite_toSet.compl_mem_cofinite, S₂.finite_toSet.compl_mem_cofinite,
    eventually_localPoints_le M₁ M₂, eventually_localPoints_le M₂ M₁] with v hv₁ hv₂ h₂₁ h₁₂
  rw [M₁.level_of_notMem hv₁, M₂.level_of_notMem hv₂]
  exact le_antisymm (h₁₂ hv₂ hv₁) (h₂₁ hv₁ hv₂)

/-- The canonical coordinatewise-identity topological group isomorphism between the restricted
products attached to two integral models `M₁` and `M₂` of `(F, H)`. -/
noncomputable def levelChangeEquiv {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    (Πʳ v, [LocalPoints F H v, M₁.level v]) ≃ₜ*
      Πʳ v, [LocalPoints F H v, M₂.level v] where
  toMulEquiv := TauCeti.restrictedProductCongr M₁.level M₂.level (M₁.eventually_level_eq M₂)
  continuous_toFun :=
    TauCeti.continuous_restrictedProductCongr M₁.level M₂.level (M₁.eventually_level_eq M₂)
  continuous_invFun :=
    TauCeti.continuous_restrictedProductCongr_symm M₁.level M₂.level (M₁.eventually_level_eq M₂)

@[simp]
theorem levelChangeEquiv_apply {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂)
    (x : Πʳ v, [LocalPoints F H v, M₁.level v]) (v : HeightOneSpectrum (𝓞 F)) :
    M₁.levelChangeEquiv M₂ x v = x v := by
  rw [levelChangeEquiv]
  exact TauCeti.restrictedProductCongr_apply M₁.level M₂.level _ x v

/-- Composing `M₁.restrictedProductEquiv` with the canonical level-change isomorphism
`M₁.levelChangeEquiv M₂` recovers `M₂.restrictedProductEquiv`. -/
@[simp]
theorem restrictedProductEquiv_trans_levelChangeEquiv {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    (M₁ : IntegralModel F H S₁) (M₂ : IntegralModel F H S₂) :
    M₁.restrictedProductEquiv.trans (M₁.levelChangeEquiv M₂) = M₂.restrictedProductEquiv := by
  ext x : 1
  ext v
  simp

end ModelIndependence

end TauCeti.IntegralModel

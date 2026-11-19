/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Smooth
public import TauCeti.NumberTheory.LocalField.Henselian
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.AdicCompletion
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Successive quotients of congruence subgroups

Let `H` be a commutative Hopf algebra over `k`, `R` a commutative `k`-algebra and `J ≤ I` ideals of
`R` with `I * I ≤ J`. A point `x` of the congruence subgroup `G(R)_I` is `ε + D` with `D` valued in
`I`; on the augmentation ideal `ker ε` it is just `D`, and modulo `J` it vanishes on products of
two elements of `ker ε`. So `x` defines a `k`-linear map from the cotangent space
`ker ε / (ker ε)²` at the identity to `I / J`, viewed as the ideal `I.map (R → R ⧸ J)` of `R ⧸ J`.
Because `I * I ≤ J`, convolution of points adds these linear maps, and a point gives zero exactly
when it lies in `G(R)_J`. Conversely every such linear map `f` comes from the point `ε + f`
of `G(R ⧸ J)`, which lifts to `G(R)` whenever points lift along `R → R ⧸ J`, for instance when `H`
is formally smooth and `R` is `J`-adically complete. Hence

  `G(R)_I / G(R)_J ≅ Hom_k(ker ε / (ker ε)², I / J)`.

For a smooth affine group `𝒢 = Spec H` over a complete discrete valuation ring `O` with maximal
ideal `m` and residue field `κ`, the cotangent space is free of some rank `d` (the dimension of the
Lie algebra of `𝒢`) and `m ^ n / m ^ (n + 1) ≅ κ`, so for `n ≥ 1`

  `|𝒢(O)_n / 𝒢(O)_{n+1}| = |κ| ^ d`.

Over the valuation ring of a nonarchimedean local field with residue field of order `q`, this is
`q ^ d`. These indices compute the volumes of congruence subgroups for Haar measure on `𝒢(O)`.

## Main declarations

* `TauCeti.HopfAlgebra.congruenceCotangentHom`: the homomorphism
  `G(R)_I → Hom_k(ker ε / (ker ε)², I / J)` for `I * I ≤ J`.
* `TauCeti.HopfAlgebra.ker_congruenceCotangentHom`: its kernel is `G(R)_J`.
* `TauCeti.HopfAlgebra.congruenceCotangentHom_surjective`: it is onto when `J ≤ I` and points lift
  along `R → R ⧸ J`; `congruenceCotangentHom_surjective_of_formallySmooth` supplies the lifting
  for formally smooth `H` and `J`-adically complete `R`.
* `TauCeti.HopfAlgebra.congruenceQuotientEquiv`: the resulting isomorphism
  `G(R)_I / G(R)_J ≃* Hom_k(ker ε / (ker ε)², I / J)`.
* `TauCeti.HopfAlgebra.natCard_quotient_congruenceSubgroup_pow_succ`: over a complete discrete
  valuation ring, `|𝒢(O)_n / 𝒢(O)_{n+1}| = |κ| ^ d` for `n ≥ 1`.
* `TauCeti.HopfAlgebra.natCard_quotient_congruenceSubgroup_pow_succ_integer`: the same over the
  valuation ring of a nonarchimedean local field.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge Stud. Adv. Math. 170 (2017), 12.5, pp. 184–185.
* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic groups and number theory*, vol. 1,
  2nd ed. (2023), §3.1, p. 126, and Lemma 3.38, p. 160.
-/

public section

open Coalgebra WithConv IsLocalRing TauCeti.Bialgebra

namespace TauCeti

namespace HopfAlgebra

variable {k H R : Type*} [CommRing k] [CommRing H] [_root_.HopfAlgebra k H]
  [CommRing R] [Algebra k R] {I J : Ideal R}

/-- Convolving two points of `G(R)_I` adds their displacements from the identity, up to an error
in `I * I`. -/
private theorem mul_apply_sub_mem {x y : WithConv (H →ₐ[k] R)}
    (hx : x ∈ congruenceSubgroup k H I) (hy : y ∈ congruenceSubgroup k H I) (h : H) :
    (x * y).ofConv h - (x.ofConv h + y.ofConv h - algebraMap k R (counit h)) ∈ I * I := by
  -- Write `x = 1 + D` and `y = 1 + D'` in the convolution algebra of linear maps.
  set D : WithConv (H →ₗ[k] R) := toConv x.ofConv.toLinearMap - 1 with hD_def
  set D' : WithConv (H →ₗ[k] R) := toConv y.ofConv.toLinearMap - 1 with hD'_def
  have hD : ∀ h, D h ∈ I := fun h ↦ by simpa [hD_def] using mem_congruenceSubgroup_iff.1 hx h
  have hD' : ∀ h, D' h ∈ I := fun h ↦ by simpa [hD'_def] using mem_congruenceSubgroup_iff.1 hy h
  have hxD : toConv x.ofConv.toLinearMap = D + 1 := by simp [hD_def]
  have hyD : toConv y.ofConv.toLinearMap = D' + 1 := by simp [hD'_def]
  have hprod : toConv (x * y).ofConv.toLinearMap = D * D' + D + D' + 1 := by
    rw [AlgHom.toLinearMap_convMul, hxD, hyD]
    noncomm_ring
  have hval := congrArg (fun f : WithConv (H →ₗ[k] R) ↦ f h) hprod
  simp only [AlgHom.toLinearMap_apply, ofConv_add, LinearMap.add_apply,
    LinearMap.convOne_apply] at hval
  have hDh : D h = x.ofConv h - algebraMap k R (counit h) := by simp [hD_def]
  have hD'h : D' h = y.ofConv h - algebraMap k R (counit h) := by simp [hD'_def]
  convert LinearMap.convMul_apply_mem_mul hD hD' h using 1
  rw [hval, hDh, hD'h]
  ring

/-- A point of `G(R)_I` takes values in `I` on the augmentation ideal. -/
private theorem apply_mem_of_mem_augmentationIdeal {x : WithConv (H →ₐ[k] R)}
    (hx : x ∈ congruenceSubgroup k H I) (a : AugmentationIdeal k H) : x.ofConv a ∈ I := by
  have ha : counit (R := k) (a : H) = 0 := a.prop
  simpa [ha] using mem_congruenceSubgroup_iff.1 hx a

variable (k H) in
/-- The value modulo `J` of a point of `G(R)_I` on the augmentation ideal, as a `k`-linear map to
`I / J`. -/
private noncomputable def augmentationValue (x : congruenceSubgroup k H I) :
    AugmentationIdeal k H →ₗ[k] I.map (Ideal.Quotient.mk J) where
  toFun a := ⟨Ideal.Quotient.mk J (x.1.ofConv a),
    Ideal.mem_map_of_mem _ (apply_mem_of_mem_augmentationIdeal x.2 a)⟩
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp [Algebra.smul_def]

variable (k H) in
/-- The linear map `ker ε / (ker ε)² → I / J` of a point of `G(R)_I`, for `I * I ≤ J`. -/
private noncomputable def cotangentValue (hIJ : I * I ≤ J) (x : congruenceSubgroup k H I) :
    CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J) :=
  Ideal.Cotangent.lift (augmentationValue k H x) fun a b ↦ by
    ext
    simpa [augmentationValue, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using
      hIJ (Ideal.mul_mem_mul (apply_mem_of_mem_augmentationIdeal x.2 a)
        (apply_mem_of_mem_augmentationIdeal x.2 b))

private theorem coe_cotangentValue_cotangentMap (hIJ : I * I ≤ J) (x : congruenceSubgroup k H I)
    (h : H) :
    (cotangentValue k H hIJ x (cotangentMap k H h) : R ⧸ J) =
      Ideal.Quotient.mk J (x.1.ofConv h - algebraMap k R (counit h)) := by
  rw [cotangentMap_apply, cotangentValue, Ideal.Cotangent.lift_toCotangent]
  simp [augmentationValue]

variable (k H) in
/-- **The graded pieces of the congruence filtration.** For ideals with `I * I ≤ J`, a point
`x ∈ G(R)_I` gives the `k`-linear map `ker ε / (ker ε)² → I / J` sending the class of `h - ε(h)`
to `x(h) - ε(h)` modulo `J`; convolution of points adds these maps. Here `I / J` is the ideal
`I.map (R → R ⧸ J)` of `R ⧸ J`. -/
noncomputable def congruenceCotangentHom (hIJ : I * I ≤ J) :
    congruenceSubgroup k H I →*
      Multiplicative (CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) where
  toFun x := .ofAdd (cotangentValue k H hIJ x)
  map_one' := by
    refine Multiplicative.toAdd.injective (LinearMap.ext fun c ↦ ?_)
    obtain ⟨h, rfl⟩ := (cotangentMap_surjective k H) c
    ext
    simp [coe_cotangentValue_cotangentMap]
  map_mul' x y := by
    refine Multiplicative.toAdd.injective (LinearMap.ext fun c ↦ ?_)
    obtain ⟨h, rfl⟩ := (cotangentMap_surjective k H) c
    ext
    simp only [toAdd_ofAdd, toAdd_mul, LinearMap.add_apply, Submodule.coe_add,
      coe_cotangentValue_cotangentMap, Subgroup.coe_mul, ← map_add]
    rw [Ideal.Quotient.eq]
    convert hIJ (mul_apply_sub_mem x.2 y.2 h) using 1
    ring

/-- The linear map of a point `x ∈ G(R)_I` sends the cotangent class of `h` to `x(h) - ε(h)`
modulo `J`. -/
@[simp]
theorem coe_congruenceCotangentHom_apply_cotangentMap (hIJ : I * I ≤ J)
    (x : congruenceSubgroup k H I) (h : H) :
    ((congruenceCotangentHom k H hIJ x).toAdd (cotangentMap k H h) : R ⧸ J) =
      Ideal.Quotient.mk J (x.1.ofConv h - algebraMap k R (counit h)) :=
  coe_cotangentValue_cotangentMap hIJ x h

/-- A point of `G(R)_I` gives the zero linear map exactly when it lies in `G(R)_J`. -/
theorem ker_congruenceCotangentHom (hIJ : I * I ≤ J) :
    (congruenceCotangentHom k H hIJ).ker =
      (congruenceSubgroup k H J).subgroupOf (congruenceSubgroup k H I) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_congruenceSubgroup_iff,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_one, LinearMap.ext_iff,
    (cotangentMap_surjective k H).forall]
  refine forall_congr' fun h ↦ ?_
  rw [LinearMap.zero_apply, ← Subtype.coe_inj, coe_congruenceCotangentHom_apply_cotangentMap,
    ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]

variable (k H) in
/-- The derivation `h ↦ f (cotangentMap h)` of `H` into `I / J`, where `H` acts on `R ⧸ J`
through the counit (`Bialgebra.CounitAlgebra`). -/
private noncomputable def cotangentDerivation
    (f : CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) :
    Derivation k H
      ((I.map (Ideal.Quotient.mk J)).comap (CounitAlgebra.algEquivSelf k H (R ⧸ J))) :=
  Derivation.mk'
    { toFun h := ⟨(CounitAlgebra.algEquivSelf k H (R ⧸ J)).symm (f (cotangentMap k H h)), by
        rw [Ideal.mem_comap, AlgEquiv.apply_symm_apply]
        exact (f _).2⟩
      map_add' a b := by ext; simp [-CounitAlgebra.algEquivSelf_symm_apply]
      map_smul' c a := by ext; simp [-CounitAlgebra.algEquivSelf_symm_apply] }
    fun a b ↦ by
      ext
      apply (CounitAlgebra.algEquivSelf k H (R ⧸ J)).injective
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Submodule.coe_smul_of_tower,
        map_add, CounitAlgebra.algEquivSelf_smul, AlgEquiv.apply_symm_apply, cotangentMap_mul,
        map_smul]
      simp only [Algebra.smul_def]

private theorem algEquivSelf_cotangentDerivation_apply
    (f : CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) (h : H) :
    CounitAlgebra.algEquivSelf k H (R ⧸ J) (cotangentDerivation k H f h) =
      f (cotangentMap k H h) :=
  AlgEquiv.apply_symm_apply _ _

variable (k H) in
/-- The point `ε + f` of `G(R ⧸ J)` attached to a linear map `f : ker ε / (ker ε)² → I / J`: the
square-zero lift of `cotangentDerivation f`, since products of two elements of `I / J` vanish when
`I * I ≤ J`. -/
private noncomputable def cotangentPoint (hIJ : I * I ≤ J)
    (f : CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) : H →ₐ[k] R ⧸ J :=
  (CounitAlgebra.algEquivSelf k H (R ⧸ J)).toAlgHom.comp <|
    liftOfDerivationToSquareZero _ (by
      refine eq_bot_iff.2 <| (pow_two _).trans_le <| Ideal.mul_le.2 fun u hu v hv ↦ ?_
      have huv := Ideal.map_mono (f := Ideal.Quotient.mk J) hIJ
        (Ideal.map_mul (Ideal.Quotient.mk J) I I ▸
          Ideal.mul_mem_mul (Ideal.mem_comap.1 hu) (Ideal.mem_comap.1 hv))
      rw [Ideal.map_quotient_self, Ideal.mem_bot, ← map_mul] at huv
      rw [Ideal.mem_bot, ← map_eq_zero_iff _ (CounitAlgebra.algEquivSelf k H (R ⧸ J)).injective]
      exact huv) (cotangentDerivation k H f)

private theorem cotangentPoint_apply (hIJ : I * I ≤ J)
    (f : CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) (h : H) :
    cotangentPoint k H hIJ f h = algebraMap k (R ⧸ J) (counit h) + f (cotangentMap k H h) := by
  rw [cotangentPoint, AlgHom.comp_apply, liftOfDerivationToSquareZero_apply, AlgEquiv.coe_toAlgHom,
    map_add, add_comm, algEquivSelf_cotangentDerivation_apply, CounitAlgebra.algebraMap_apply]
  exact congrArg (· + _) (CounitAlgebra.algEquivSelf_apply k H (R ⧸ J) _)

/-- **Every graded piece is attained.** If `J ≤ I`, `I * I ≤ J` and every point of `G(R ⧸ J)` lifts
to `G(R)`, then every linear map `ker ε / (ker ε)² → I / J` comes from a point of `G(R)_I`: lift
the point `ε + f` of `G(R ⧸ J)`. -/
theorem congruenceCotangentHom_surjective (hIJ : I * I ≤ J) (hJI : J ≤ I)
    (hlift : Function.Surjective
      ((Ideal.Quotient.mkₐ k J).comp : (H →ₐ[k] R) → H →ₐ[k] R ⧸ J)) :
    Function.Surjective (congruenceCotangentHom k H hIJ) := by
  intro f
  obtain ⟨x, hx⟩ := hlift (cotangentPoint k H hIJ f.toAdd)
  have hval (h : H) : Ideal.Quotient.mk J (x h - algebraMap k R (counit h)) =
      f.toAdd (cotangentMap k H h) := by
    have hxh := congrArg (· h) hx
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, cotangentPoint_apply] at hxh
    rw [map_sub, hxh, Ideal.Quotient.mk_algebraMap, add_sub_cancel_left]
  have hmem : toConv x ∈ congruenceSubgroup k H I := by
    refine mem_congruenceSubgroup_iff.2 fun h ↦ ?_
    have hf := (f.toAdd (cotangentMap k H h)).2
    rwa [← hval, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.2 hJI] at hf
  refine ⟨⟨toConv x, hmem⟩, Multiplicative.toAdd.injective (LinearMap.ext fun c ↦ ?_)⟩
  obtain ⟨h, rfl⟩ := (cotangentMap_surjective k H) c
  ext
  rw [coe_congruenceCotangentHom_apply_cotangentMap]
  exact hval h

/-- For formally smooth `H` and `J`-adically complete `R`, every linear map
`ker ε / (ker ε)² → I / J` comes from a point of `G(R)_I`, when `J ≤ I` and `I * I ≤ J`. -/
theorem congruenceCotangentHom_surjective_of_formallySmooth [Algebra.FormallySmooth k H]
    [IsAdicComplete J R] (hIJ : I * I ≤ J) (hJI : J ≤ I) :
    Function.Surjective (congruenceCotangentHom k H hIJ) :=
  congruenceCotangentHom_surjective hIJ hJI
    Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete

variable (k H) in
/-- **The successive quotients of the congruence filtration.** If `J ≤ I`, `I * I ≤ J` and points
lift along `R → R ⧸ J`, then `G(R)_I / G(R)_J` is isomorphic to the additive group of `k`-linear
maps from the cotangent space `ker ε / (ker ε)²` at the identity to `I / J`. -/
noncomputable def congruenceQuotientEquiv (hIJ : I * I ≤ J) (hJI : J ≤ I)
    (hlift : Function.Surjective
      ((Ideal.Quotient.mkₐ k J).comp : (H →ₐ[k] R) → H →ₐ[k] R ⧸ J)) :
    congruenceSubgroup k H I ⧸ (congruenceSubgroup k H J).subgroupOf (congruenceSubgroup k H I) ≃*
      Multiplicative (CotangentSpace k H →ₗ[k] I.map (Ideal.Quotient.mk J)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_congruenceCotangentHom hIJ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (congruenceCotangentHom_surjective hIJ hJI hlift))

/-- The isomorphism `congruenceQuotientEquiv` sends the class of `x` to the linear map
`congruenceCotangentHom x`. -/
@[simp]
theorem congruenceQuotientEquiv_mk (hIJ : I * I ≤ J) (hJI : J ≤ I)
    (hlift : Function.Surjective
      ((Ideal.Quotient.mkₐ k J).comp : (H →ₐ[k] R) → H →ₐ[k] R ⧸ J))
    (x : congruenceSubgroup k H I) :
    congruenceQuotientEquiv k H hIJ hJI hlift x = congruenceCotangentHom k H hIJ x := by
  simp only [congruenceQuotientEquiv, MulEquiv.trans_apply]
  exact QuotientGroup.kerLift_mk (congruenceCotangentHom k H hIJ) x

section DiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {H : Type*} [CommRing H] [_root_.HopfAlgebra O H]

/-- **Indices of the congruence filtration of a smooth group.** Let `𝒢 = Spec H` be an affine group
over a complete discrete valuation ring `O` with maximal ideal `m` and residue field `κ`, with `H`
formally smooth and of finite type over `O`, and let `d` be the rank of the free `O`-module
`ker ε / (ker ε)²`. For `n ≥ 1`, the quotient `𝒢(O)_n / 𝒢(O)_{n+1}` of successive congruence
subgroups has `|κ| ^ d` elements. When `κ` is infinite and `d ≠ 0`, both sides are `0`. -/
theorem natCard_quotient_congruenceSubgroup_pow_succ [IsAdicComplete (maximalIdeal O) O]
    [Algebra.FormallySmooth O H] [Algebra.FiniteType O H] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (congruenceSubgroup O H (maximalIdeal O ^ n) ⧸
        (congruenceSubgroup O H (maximalIdeal O ^ (n + 1))).subgroupOf
          (congruenceSubgroup O H (maximalIdeal O ^ n))) =
      Nat.card (ResidueField O) ^ Module.finrank O (CotangentSpace O H) := by
  have hIJ : maximalIdeal O ^ n * maximalIdeal O ^ n ≤ maximalIdeal O ^ (n + 1) := by
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by omega)
  have hJI : maximalIdeal O ^ (n + 1) ≤ maximalIdeal O ^ n := Ideal.pow_le_pow_right n.le_succ
  have : IsAdicComplete (maximalIdeal O ^ (n + 1)) O := IsAdicComplete.pow n.succ_ne_zero
  -- The cotangent space is finite projective, hence free over the local ring `O`.
  have : Module.Free O (CotangentSpace O H) := Module.free_of_flat_of_isLocalRing
  rw [Nat.card_congr (congruenceQuotientEquiv O H hIJ hJI
      Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete).toEquiv,
    Nat.card_congr Multiplicative.toAdd,
    Nat.card_congr ((Module.finBasis O (CotangentSpace O H)).constr O).symm.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin,
    TauCeti.IsDiscreteValuationRing.natCard_map_maximalIdeal_pow]

end DiscreteValuationRing

section LocalField

open ValuativeRel

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {H : Type*} [CommRing H] [_root_.HopfAlgebra 𝒪[E] H]

/-- **Indices of the congruence filtration over a local field.** Let `𝒢 = Spec H` be a smooth affine
group over the valuation ring `O = 𝒪[E]` of a nonarchimedean local field whose residue field has `q`
elements, and let `d` be the rank of the free `O`-module `ker ε / (ker ε)²`, the dimension of the
Lie algebra of `𝒢`. For `n ≥ 1`, `𝒢(O)_n / 𝒢(O)_{n+1}` has `q ^ d` elements. -/
theorem natCard_quotient_congruenceSubgroup_pow_succ_integer [Algebra.FormallySmooth 𝒪[E] H]
    [Algebra.FiniteType 𝒪[E] H] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (congruenceSubgroup 𝒪[E] H (𝓂[E] ^ n) ⧸
        (congruenceSubgroup 𝒪[E] H (𝓂[E] ^ (n + 1))).subgroupOf
          (congruenceSubgroup 𝒪[E] H (𝓂[E] ^ n))) =
      Nat.card 𝓀[E] ^ Module.finrank 𝒪[E] (CotangentSpace 𝒪[E] H) := by
  -- Mathlib's completeness of `𝒪[E]` is stated for the uniformity of the additive group `E`.
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  let _ := isUniformAddGroup_of_addCommGroup (G := E)
  exact natCard_quotient_congruenceSubgroup_pow_succ hn

end LocalField

end HopfAlgebra

end TauCeti

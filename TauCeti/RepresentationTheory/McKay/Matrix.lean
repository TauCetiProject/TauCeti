/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Multiplicity
public import TauCeti.RepresentationTheory.FDRep.Dual
public import TauCeti.RepresentationTheory.Tensor.Power
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.LinearAlgebra.Determinant.FiniteOrder
import TauCeti.RepresentationTheory.CharacterTable.Degree
import TauCeti.RepresentationTheory.InvariantForm.Determinant
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic

/-!
# The McKay matrix and tensor-power multiplicities

For an object `V` of `FDRep k G`, the **McKay matrix** `TauCeti.mckayMatrix V` is the matrix indexed
by the isomorphism classes `TauCeti.SimpleFDRepClasses k G` of simple objects of `FDRep k G` whose
`(c₁, c₂)` entry is the multiplicity `dim_k Hom_G(X, V ⊗ Y)` of `c₁ = [X]` in `V ⊗ Y` for
`c₂ = [Y]`.

This file develops the representation-theoretic properties of `mckayMatrix V` that drive Steinberg's
proof of the McKay correspondence in `TauCeti.RepresentationTheory.McKay.Basic`:

1. **Loop-freeness** (`FDRep.finrank_hom_tensor_self_eq_zero`,
   `TauCeti.mckayMatrix_apply_self_eq_zero`): when `G` is a nontrivial finite group and `V` is a
   faithful two-dimensional representation of determinant `1` over an algebraically closed field of
   characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. If `V` is irreducible,
   `2 = dim V ∣ |G|` (`FDRep.finrank_dvd_card`), Cauchy's theorem produces an element `g₀` of order
   `2`, and uniqueness of the determinant-one involution
   (`LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one`) forces `V.ρ g₀ = -1`. If `V`
   is reducible, Maschke's theorem splits `V` via `Subrepresentation.equivProdOfIsCompl` into two
   one-dimensional subrepresentations whose product of eigenvalues is `1`, making `G` abelian and
   producing a non-identity element whose eigenvalues on `V` both differ from `1`.
2. **Duality and symmetry** (`TauCeti.mckayMatrix_transpose`,
   `TauCeti.isSymm_mckayMatrix_of_equiv_dual`, `TauCeti.isSymm_mckayMatrix`): when `|G|` is
   invertible in `k`, Frobenius reciprocity gives `(mckayMatrix V)ᵀ = mckayMatrix (ᘁV)`; when `V`
   is self-dual — in particular when `dim_k V = 2` and `∀ g, det (V.ρ g) = 1`
   (`Representation.equivDualOfFinrankEqTwo`) — `mckayMatrix V` is symmetric.
3. **Null vector** (`TauCeti.sum_mckayMatrix_mul_finrank_left`,
   `TauCeti.sum_mckayMatrix_mul_finrank`): decomposing `V ⊗ Y` into simples and passing through
   `ᘁV` shows that for every `V : FDRep k G`, the vector `δ` of irreducible dimensions
   (`TauCeti.SimpleFDRepClasses.finrank`) satisfies `M δ = (dim V) δ`, with `δ > 0` and `δ = 1` at
   `TauCeti.SimpleFDRepClasses.trivial k G`.
4. **Tensor-power multiplicities** (`TauCeti.mckayMatrix_pow_apply`,
   `TauCeti.mckayMatrix_pow_apply_trivial`): `(mckayMatrix V ^ n) c₁ [Y]` equals the multiplicity of
   `c₁` in `V^⊗n ⊗ Y`, and in particular `(mckayMatrix V ^ n) c trivial` is the multiplicity of `c`
   in `V^⊗n`.

## Main definitions

* `TauCeti.mckayMatrix`: the matrix `(c₁, c₂) ↦ dim_k Hom_G(X, V ⊗ Y)` on `SimpleFDRepClasses k G`.

## Main results

* `FDRep.finrank_hom_tensor_self_eq_zero` and `TauCeti.mckayMatrix_apply_self_eq_zero`:
  loop-freeness for faithful two-dimensional representations of determinant `1`.
* `TauCeti.mckayMatrix_transpose`, `TauCeti.isSymm_mckayMatrix_of_equiv_dual`, and
  `TauCeti.isSymm_mckayMatrix`: transpose via `ᘁV` and symmetry of `mckayMatrix V`.
* `TauCeti.sum_mckayMatrix_mul_finrank_left` and `TauCeti.sum_mckayMatrix_mul_finrank`:
  column-sum identity and unconditional null-vector equation `M δ = (dim V) δ`.
* `TauCeti.mckayMatrix_pow_apply` and `TauCeti.mckayMatrix_pow_apply_trivial`: powers of
  `mckayMatrix V` compute tensor-power multiplicities.

## References

* J. McKay, *Graphs, singularities, and finite groups*, Proc. Symp. Pure Math. **37** (1980),
  183–186.
* R. Steinberg, *Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*, Pacific J.
  Math. **118** (1985), 587–598.
-/

public section

open CategoryTheory MonoidalCategory Finset
open scoped MonoidAlgebra TensorProduct

universe u v

/-! ### Loop-freeness of faithful rank-two representations of determinant one -/

namespace FDRep

section LoopFree

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- If `g₀ : G` commutes with `G` and `(V.ρ g₀ - c₁ • id) ∘ (V.ρ g₀ - c₂ • id) = 0` with
`c₁ ≠ 1` and `c₂ ≠ 1`, then over an algebraically closed field no simple `X` admits a nonzero
intertwiner `X ⟶ V ⊗ X`. -/
private theorem finrank_hom_tensor_self_eq_zero_of_central [IsAlgClosed k] {V : FDRep k G}
    {g₀ : G} (hcomm : ∀ h : G, g₀ * h = h * g₀) {c₁ c₂ : k} (hc₁ : c₁ ≠ 1) (hc₂ : c₂ ≠ 1)
    (hann : (V.ρ g₀ - c₁ • LinearMap.id) ∘ₗ (V.ρ g₀ - c₂ • LinearMap.id) = 0)
    (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  have hX : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  obtain ⟨μ, hμ⟩ := hX.exists_forall_apply_eq_smul (X.ρ g₀) fun h x ↦ by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hcomm h]
  have hμ0 : μ ≠ 0 := by
    have : Nontrivial X := hX.nontrivial
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
    rintro rfl
    apply hx₀
    calc
      x₀ = X.ρ (g₀⁻¹ * g₀) x₀ := by simp
      _ = X.ρ g₀⁻¹ (X.ρ g₀ x₀) := by rw [map_mul, mul_apply_eq_comp]
      _ = 0 := by rw [hμ x₀, zero_smul, map_zero]
  suffices Subsingleton (X ⟶ V ⊗ X) from Module.finrank_zero_of_subsingleton
  refine ⟨fun φ ψ ↦ sub_eq_zero.mp ?_⟩
  set f : X ⟶ V ⊗ X := φ - ψ
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  set z : V ⊗[k] X := f.hom.hom.hom x
  have heq : (V ⊗ X).ρ g₀ z = μ • z := by
    have hc := LinearMap.congr_fun (FDRep.hom_hom_hom_comm f g₀) x
    simp only [LinearMap.comp_apply, hμ x, map_smul] at hc
    exact hc.symm
  have htens : (V ⊗ X).ρ g₀ = μ • (V.ρ g₀).rTensor X := by
    rw [FDRep.tensor_ρ, show X.ρ g₀ = μ • LinearMap.id from LinearMap.ext hμ]
    exact TensorProduct.ext' fun v y ↦ by simp [TensorProduct.tmul_smul]
  rw [htens, LinearMap.smul_apply] at heq
  have hz : (V.ρ g₀).rTensor X z = z := smul_right_injective _ hμ0 heq
  have hz_sub (c : k) : ((V.ρ g₀ - c • LinearMap.id).rTensor X) z = (1 - c) • z := by
    simp [hz, sub_smul]
  have hzero : ((1 - c₁) * (1 - c₂)) • z = 0 := by
    rw [← smul_smul]
    calc
      (1 - c₁) • ((1 - c₂) • z) =
          ((V.ρ g₀ - c₁ • LinearMap.id).rTensor X) ((1 - c₂) • z) := by
        rw [map_smul, hz_sub c₁, smul_comm]
      _ = (((V.ρ g₀ - c₁ • LinearMap.id) ∘ₗ (V.ρ g₀ - c₂ • LinearMap.id)).rTensor X) z := by
        rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hz_sub c₂]
      _ = 0 := by rw [hann, LinearMap.rTensor_zero, LinearMap.zero_apply]
  have hz0 : z = 0 :=
    (smul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr hc₁.symm) (sub_ne_zero.mpr hc₂.symm))
  simpa [z] using hz0

/-- A reducible two-dimensional semisimple faithful representation of a nontrivial finite group
with determinant `1` splits via `Subrepresentation.equivProdOfIsCompl` into two dual one-dimensional
summands, making `G` abelian and producing `g₀ : G` whose eigenvalues `c₁, c₂` both differ from `1`
and annihilate `V.ρ g₀`. -/
private theorem exists_central_annihilator_of_not_simple [Finite G] [Nontrivial G]
    [NeZero (Nat.card G : k)] {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hfaithful : Function.Injective V.ρ) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1)
    (hV : ¬ Simple V) :
    ∃ (g₀ : G) (c₁ c₂ : k), (∀ h : G, g₀ * h = h * g₀) ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧
      (V.ρ g₀ - c₁ • LinearMap.id) ∘ₗ (V.ρ g₀ - c₂ • LinearMap.id) = 0 := by
  have hV_not : ¬ Representation.IsIrreducible V.ρ :=
    fun h ↦ hV (FDRep.simple_of_isIrreducible V)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (hdim ▸ zero_lt_two)
  obtain ⟨W, hW_bot, hW_top⟩ : ∃ W : Subrepresentation V.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra! hall
    exact hV_not ⟨fun W ↦ or_iff_not_imp_left.mpr (hall W)⟩
  have : Representation.IsSemisimpleRepresentation V.ρ :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule V.ρ).mpr
      inferInstance
  obtain ⟨W', hWW'⟩ := exists_isCompl W
  let e := Subrepresentation.equivProdOfIsCompl hWW'
  have hW_pos : 0 < Module.finrank k W.toSubmodule := by
    have hne : W.toSubmodule ≠ ⊥ := fun h ↦
      hW_bot (Subrepresentation.toSubmodule_injective
        (h.trans Subrepresentation.toSubmodule_bot.symm))
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W.toSubmodule).mp hne
    have : Nontrivial W.toSubmodule := ⟨⟨⟨w, hw⟩, 0, Subtype.coe_ne_coe.mp hw0⟩⟩
    exact Module.finrank_pos
  have hW_lt : Module.finrank k W.toSubmodule < 2 := by
    have hlt : W.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr fun h ↦
      hW_top (Subrepresentation.toSubmodule_injective
        (h.trans Subrepresentation.toSubmodule_top.symm))
    simpa [hdim] using Submodule.finrank_lt_finrank_of_lt hlt
  have hW1 : Module.finrank k W.toSubmodule = 1 := by omega
  have hW'1 : Module.finrank k W'.toSubmodule = 1 := by
    have hsum := e.toLinearEquiv.finrank_eq
    rw [hdim, Module.finrank_prod, hW1] at hsum
    omega
  choose c₁ hc₁ using fun g : G ↦
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW1 (W.toRepresentation g)).exists
  choose c₂ hc₂ using fun g : G ↦
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW'1 (W'.toRepresentation g)).exists
  have he_apply (g : G) (v : V) : e (V.ρ g v) = (c₁ g • (e v).1, c₂ g • (e v).2) := by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    have hp : (W.toRepresentation.prod W'.toRepresentation) g =
        LinearMap.prodMap (c₁ g • LinearMap.id) (c₂ g • LinearMap.id) := by
      rw [← hc₁ g, ← hc₂ g]
      rfl
    simpa [hp] using h
  let eL : V ≃ₗ[k] W.toSubmodule × W'.toSubmodule := e.toLinearEquiv
  have hconj (g : G) :
      (eL : V →ₗ[k] W.toSubmodule × W'.toSubmodule) ∘ₗ V.ρ g ∘ₗ
          (eL.symm : W.toSubmodule × W'.toSubmodule →ₗ[k] V) =
        LinearMap.prodMap (c₁ g • LinearMap.id) (c₂ g • LinearMap.id) := by
    refine LinearMap.ext fun p ↦ ?_
    change e (V.ρ g (eL.symm p)) = (c₁ g • p.1, c₂ g • p.2)
    rw [he_apply]
    change (c₁ g • (eL (eL.symm p)).1, c₂ g • (eL (eL.symm p)).2) = (c₁ g • p.1, c₂ g • p.2)
    simp
  have hdet_prod (g : G) : c₁ g * c₂ g = 1 := by
    have hd : LinearMap.det
        ((eL : V →ₗ[k] W.toSubmodule × W'.toSubmodule) ∘ₗ V.ρ g ∘ₗ
          (eL.symm : W.toSubmodule × W'.toSubmodule →ₗ[k] V)) = 1 := by
      rw [LinearMap.det_conj, hdet g]
    rw [hconj g, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul, LinearMap.det_id,
      LinearMap.det_id, hW1, hW'1, pow_one, pow_one, mul_one, mul_one] at hd
    exact hd
  have hcomm (g h : G) : g * h = h * g :=
    hfaithful <| LinearMap.ext fun v ↦ e.toLinearEquiv.injective <| by
      simp [map_mul, mul_apply_eq_comp, he_apply, smul_smul, mul_comm]
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
  have hne_one : ¬ (c₁ g₀ = 1 ∧ c₂ g₀ = 1) := by
    rintro ⟨h1, h2⟩
    apply hg₀ (hfaithful ?_)
    rw [map_one]
    exact LinearMap.ext fun v ↦ e.toLinearEquiv.injective (by simp [he_apply, h1, h2])
  have hc₁_ne : c₁ g₀ ≠ 1 := fun h1 ↦
    hne_one ⟨h1, by have := hdet_prod g₀; rw [h1, one_mul] at this; exact this⟩
  have hc₂_ne : c₂ g₀ ≠ 1 := fun h2 ↦
    hne_one ⟨by have := hdet_prod g₀; rw [h2, mul_one] at this; exact this, h2⟩
  refine ⟨g₀, c₁ g₀, c₂ g₀, fun h ↦ hcomm g₀ h, hc₁_ne, hc₂_ne, LinearMap.ext fun v ↦ ?_⟩
  apply e.toLinearEquiv.injective
  ext <;> simp [he_apply, smul_sub, smul_smul, mul_comm]

/-- **Loop-freeness of the McKay graph.** For a nontrivial finite group `G` and a faithful
two-dimensional representation `V : FDRep k G` of determinant `1` over an algebraically closed
field `k` of characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. -/
theorem finrank_hom_tensor_self_eq_zero [IsAlgClosed k] [CharZero k] [Finite G] [Nontrivial G]
    (V : FDRep k G) (hdim : Module.finrank k V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  by_cases hV : Simple V
  · -- Irreducible branch: `2 ∣ |G|`, Cauchy's theorem produces an order-2 element acting as `-1`.
    have : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
    have hdvd : 2 ∣ Nat.card G := hdim ▸ FDRep.finrank_dvd_card V
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hg₀_ne : g₀ ≠ 1 := fun h1 ↦ by simp [h1] at hg₀
    have hg₀_sq : V.ρ g₀ * V.ρ g₀ = 1 := by
      rw [← map_mul, ← sq, ← hg₀, pow_orderOf_eq_one, map_one]
    have hVg₀ : V.ρ g₀ = -1 :=
      (LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one two_ne_zero hdim hg₀_sq
        (hdet g₀)).resolve_left fun h1 ↦ hg₀_ne (hfaithful (h1.trans (map_one V.ρ).symm))
    have hcomm (h : G) : g₀ * h = h * g₀ := hfaithful <| by
      rw [map_mul, map_mul, hVg₀, neg_one_mul, mul_neg_one]
    have hneg1 : (-1 : k) ≠ 1 := fun h ↦ (two_ne_zero : (2 : k) ≠ 0) <| by
      have h2 := congrArg (· + (1 : k)) h
      rw [neg_add_cancel, one_add_one_eq_two] at h2
      exact h2.symm
    refine finrank_hom_tensor_self_eq_zero_of_central hcomm hneg1 hneg1 ?_ X
    ext v
    simp [hVg₀]
  · -- Reducible branch: split `V` into two `1`-dimensional summands of inverse characters.
    have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨g₀, c₁, c₂, hcomm, hc₁, hc₂, hann⟩ :=
      exists_central_annihilator_of_not_simple hdim hfaithful hdet hV
    exact finrank_hom_tensor_self_eq_zero_of_central hcomm hc₁ hc₂ hann X

end LoopFree

end FDRep

namespace TauCeti

/-! ### The McKay matrix and tensor-power multiplicities -/

section McKayMatrix

variable {k : Type u} {G : Type v} [Field k]

/-- **The McKay matrix** of `V : FDRep k G`, indexed by `SimpleFDRepClasses k G`, with `(c₁, c₂)`
entry `dim_k Hom_G(X, V ⊗ Y)` for representatives `c₁ = [X]` and `c₂ = [Y]`. -/
noncomputable def mckayMatrix [Monoid G] (V : FDRep k G) :
    Matrix (SimpleFDRepClasses k G) (SimpleFDRepClasses k G) ℕ :=
  fun c₁ c₂ ↦ c₂.lift (fun Y ↦ c₁.multiplicity (V ⊗ Y)) fun _ _ _ _ ⟨iso⟩ ↦
    c₁.multiplicity_congr (whiskerLeftIso V iso)

@[simp]
theorem mckayMatrix_apply_mk [Monoid G] (V : FDRep k G) (c₁ : SimpleFDRepClasses k G)
    (Y : FDRep k G) [Simple Y] :
    mckayMatrix V c₁ (SimpleFDRepClasses.mk Y) = c₁.multiplicity (V ⊗ Y) :=
  SimpleFDRepClasses.lift_mk Y

/-- Entry `(mk X, mk Y)` of `mckayMatrix V` is `dim_k Hom_G(X, V ⊗ Y)`. -/
theorem mckayMatrix_mk_mk [Monoid G] (V X Y : FDRep k G) [Simple X] [Simple Y] :
    mckayMatrix V (SimpleFDRepClasses.mk X) (SimpleFDRepClasses.mk Y) =
      Module.finrank k (X ⟶ V ⊗ Y) := by
  rw [mckayMatrix_apply_mk, SimpleFDRepClasses.multiplicity_mk]

/-- Isomorphic objects in `FDRep k G` have the same McKay matrix. -/
theorem mckayMatrix_congr [Monoid G] {V₁ V₂ : FDRep k G} (iso : V₁ ≅ V₂) :
    mckayMatrix V₁ = mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, mckayMatrix_apply_mk]
    exact c₁.multiplicity_congr (whiskerRightIso iso Y)

/-- **Transpose of the McKay matrix.** When `|G|` is invertible in `k`, `(mckayMatrix V)ᵀ` is the
McKay matrix of the categorical left dual `ᘁV`. -/
@[simp]
theorem mckayMatrix_transpose [Group G] [Invertible (Nat.card G : k)] (V : FDRep k G) :
    (mckayMatrix V).transpose = mckayMatrix (ᘁV) := by
  ext c₁ c₂
  induction c₁ using SimpleFDRepClasses.ind with
  | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [Matrix.transpose_apply, mckayMatrix_mk_mk, mckayMatrix_mk_mk]
    exact FDRep.finrank_hom_tensor_leftDual V Y X

/-- **Symmetry of the McKay matrix** for a self-dual representation when `|G|` is invertible in
`k`. -/
theorem isSymm_mckayMatrix_of_equiv_dual [Group G] [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (_root_.Representation.dual V.ρ))) :
    (mckayMatrix V).IsSymm := by
  obtain ⟨e⟩ := he
  rw [Matrix.IsSymm, mckayMatrix_transpose]
  exact mckayMatrix_congr (FDRep.isoLeftDualOfEquivDual e).symm

/-- **Symmetry of the McKay matrix** for a two-dimensional representation of determinant `1` when
`|G|` is invertible in `k`. -/
theorem isSymm_mckayMatrix [Group G] [Invertible (Nat.card G : k)] {V : FDRep k G}
    (hdim : Module.finrank k V = 2) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    (mckayMatrix V).IsSymm :=
  isSymm_mckayMatrix_of_equiv_dual ⟨_root_.Representation.equivDualOfFinrankEqTwo V.ρ hdim hdet⟩

/-- **Diagonal vanishing of the McKay matrix** for a faithful two-dimensional representation of
determinant `1` of a nontrivial finite group over an algebraically closed field of characteristic
zero. -/
theorem mckayMatrix_apply_self_eq_zero [IsAlgClosed k] [CharZero k] [Group G] [Finite G]
    [Nontrivial G] {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hfaithful : Function.Injective V.ρ) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1)
    (c : SimpleFDRepClasses k G) :
    mckayMatrix V c c = 0 := by
  induction c using SimpleFDRepClasses.ind with
  | h X hX =>
    rw [mckayMatrix_mk_mk]
    exact FDRep.finrank_hom_tensor_self_eq_zero V hdim hfaithful hdet X

section Semisimple

variable [IsAlgClosed k] [Group G] [Finite G] [Invertible (Nat.card G : k)]

/-- Column sum of `mckayMatrix V` against the irreducible dimensions:
`∑ c₁, mckayMatrix V c₁ c₂ * c₁.finrank = dim V * c₂.finrank`. -/
theorem sum_mckayMatrix_mul_finrank_left [Fintype (SimpleFDRepClasses k G)] (V : FDRep k G)
    (c₂ : SimpleFDRepClasses k G) :
    ∑ c₁ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₁.finrank =
      Module.finrank k V * c₂.finrank := by
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    simp_rw [mckayMatrix_apply_mk, SimpleFDRepClasses.finrank_mk]
    rw [← finrank_eq_sum_multiplicity_mul_finrank (V ⊗ Y), FDRep.finrank_tensor]

/-- **Null-vector equation `M δ = (dim V) δ`** for every finite-dimensional representation `V`. -/
theorem sum_mckayMatrix_mul_finrank [Fintype (SimpleFDRepClasses k G)] (V : FDRep k G)
    (c₁ : SimpleFDRepClasses k G) :
    ∑ c₂ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₂.finrank =
      Module.finrank k V * c₁.finrank := by
  have hentry (c₂ : SimpleFDRepClasses k G) :
      mckayMatrix V c₁ c₂ = mckayMatrix (ᘁV) c₂ c₁ := by
    rw [← mckayMatrix_transpose, Matrix.transpose_apply]
  simp_rw [hentry]
  rw [sum_mckayMatrix_mul_finrank_left (ᘁV) c₁, FDRep.finrank_leftDual]

/-- **Multiplicity in `V ⊗ W` expands by matrix-vector multiplication with `mckayMatrix V`.** -/
theorem multiplicity_tensor_eq_sum [Fintype (SimpleFDRepClasses k G)] (V W : FDRep k G)
    (c₁ : SimpleFDRepClasses k G) :
    c₁.multiplicity (V ⊗ W) =
      ∑ c₂ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₂.multiplicity W := by
  classical
  obtain ⟨eW⟩ := _root_.Representation.nonempty_equiv_directSum_irreducibleRepresentation W.ρ
  let j := SimpleFDRepClasses.equivFinCardConjClasses k G c₁
  have hc₁ : c₁ = (SimpleFDRepClasses.equivFinCardConjClasses k G).symm j :=
    ((SimpleFDRepClasses.equivFinCardConjClasses k G).symm_apply_apply c₁).symm
  have hlhs : c₁.multiplicity (V ⊗ W) =
      _root_.Representation.intrinsicMultiplicity ((V ⊗ W : FDRep k G)).ρ j := by
    rw [hc₁, SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm]
  rw [hlhs]
  have heq : _root_.Representation.Equiv ((V ⊗ W : FDRep k G)).ρ
      (_root_.Representation.directSum
        fun s : Σ i : Fin (Nat.card (ConjClasses G)),
            Fin (_root_.Representation.intrinsicMultiplicity W.ρ i) ↦
          _root_.Representation.tprod V.ρ (irreducibleRepresentation k s.1)) :=
    (FDRep.tensorEquivTprod V W).trans
      (((_root_.Representation.Equiv.refl V.ρ).tprod eW).trans
        (_root_.Representation.tprodDirectSumEquiv V.ρ _))
  rw [_root_.Representation.intrinsicMultiplicity_congr heq,
    _root_.Representation.intrinsicMultiplicity_directSum, Fintype.sum_sigma]
  have hinner (i : Fin (Nat.card (ConjClasses G))) :
      (∑ _ : Fin (_root_.Representation.intrinsicMultiplicity W.ρ i),
          (_root_.Representation.tprod V.ρ
            (irreducibleRepresentation k i)).intrinsicMultiplicity j) =
        _root_.Representation.intrinsicMultiplicity W.ρ i *
          (_root_.Representation.tprod V.ρ
            (irreducibleRepresentation k i)).intrinsicMultiplicity j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp_rw [hinner]
  refine Finset.sum_equiv (SimpleFDRepClasses.equivFinCardConjClasses k G).symm
    (s := univ) (t := univ) (fun _ ↦ by simp) fun i _ ↦ ?_
  rw [SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm,
    SimpleFDRepClasses.equivFinCardConjClasses_symm_apply, mckayMatrix_apply_mk,
    hc₁, SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm, mul_comm]
  rfl

/-- **Powers of the McKay matrix count tensor-power multiplicities.** For every `n : ℕ`,
`(mckayMatrix V ^ n) c₁ (mk Y) = c₁.multiplicity (V.tensorPower n ⊗ Y)`. -/
theorem mckayMatrix_pow_apply [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ)
    (c₁ : SimpleFDRepClasses k G) (Y : FDRep k G) [Simple Y] :
    (mckayMatrix V ^ n) c₁ (SimpleFDRepClasses.mk Y) =
      c₁.multiplicity (V.tensorPower n ⊗ Y) := by
  induction n generalizing c₁ with
  | zero =>
    rw [pow_zero, Matrix.one_apply,
      c₁.multiplicity_congr (whiskerRightIso V.tensorPowerZeroIsoTensorUnit Y ≪≫ λ_ Y),
      c₁.multiplicity_simple Y]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← multiplicity_tensor_eq_sum V (V.tensorPower n ⊗ Y) c₁]
    exact c₁.multiplicity_congr
      ((whiskerRightIso (V.tensorPowerSuccIso n) Y ≪≫ α_ V (V.tensorPower n) Y).symm)

/-- **Entries at the trivial column of `mckayMatrix V ^ n` count multiplicities in `V^⊗n`.** -/
theorem mckayMatrix_pow_apply_trivial [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ)
    (c : SimpleFDRepClasses k G) :
    (mckayMatrix V ^ n) c (SimpleFDRepClasses.trivial k G) = c.multiplicity (V.tensorPower n) := by
  rw [← SimpleFDRepClasses.mk_tensorUnit, mckayMatrix_pow_apply]
  exact c.multiplicity_congr (ρ_ (V.tensorPower n))

end Semisimple

end McKayMatrix

end TauCeti

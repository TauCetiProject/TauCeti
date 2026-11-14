/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.IrreducibleClassification
public import TauCeti.RepresentationTheory.CharacterTable.Multiplicity
public import TauCeti.RepresentationTheory.Tensor.Power
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import TauCeti.LinearAlgebra.Determinant.FiniteOrder
import TauCeti.RepresentationTheory.CharacterTable.Degree
import TauCeti.RepresentationTheory.InvariantForm.Determinant

/-!
# The McKay matrix and tensor-power multiplicities

For an object `V` of `FDRep k G`, the **McKay matrix** `TauCeti.mckayMatrix V` is the matrix indexed
by the isomorphism classes `TauCeti.SimpleFDRepClasses k G` of simple objects of `FDRep k G` whose
`(c₁, c₂)` entry is the multiplicity `dim_k Hom_G(X, V ⊗ Y)` of `c₁ = [X]` in `V ⊗ Y` for
`c₂ = [Y]`.

This file develops the representation-theoretic properties of `mckayMatrix V` that drive Steinberg's
proof of the McKay correspondence in `TauCeti.RepresentationTheory.McKay`:

1. **Loop-freeness** (`FDRep.finrank_hom_tensor_self_eq_zero`,
   `TauCeti.mckayMatrix_apply_self_eq_zero`): when `G` is a nontrivial finite group and `V` is a
   faithful two-dimensional representation of determinant `1` over an algebraically closed field of
   characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. If `V` is irreducible,
   `2 = dim V ∣ |G|` (`FDRep.finrank_dvd_card`), Cauchy's theorem produces an element `g₀` of order
   `2`, and uniqueness of the determinant-one involution
   (`LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one`) forces `V.ρ g₀ = -1`. If `V`
   is reducible, Maschke's theorem splits `V` into two one-dimensional subrepresentations whose
   product of eigenvalues is `1`, making `G` abelian and producing a non-identity element whose
   eigenvalues on `V` both differ from `1`.
2. **Symmetry** (`TauCeti.isSymm_mckayMatrix_of_equiv_dual`, `TauCeti.isSymm_mckayMatrix`): when
   `|G|` is invertible in `k` and `V` is self-dual — in particular when `dim_k V = 2` and
   `∀ g, det (V.ρ g) = 1` (`Representation.equivDualOfFinrankEqTwo`) — Frobenius reciprocity makes
   `mckayMatrix V` symmetric.
3. **Null vector** (`TauCeti.finrank_eq_sum_multiplicity_mul_finrank`,
   `TauCeti.sum_mckayMatrix_mul_finrank`): decomposing `V ⊗ Y` into simples shows that the vector
   `δ` of irreducible dimensions (`TauCeti.SimpleFDRepClasses.finrank`) satisfies
   `M δ = (dim V) δ`, with `δ > 0` and `δ = 1` at `TauCeti.SimpleFDRepClasses.trivial k G`.
4. **Tensor-power multiplicities** (`TauCeti.mckayMatrix_pow_apply`,
   `TauCeti.mckayMatrix_pow_apply_trivial`): `(mckayMatrix V ^ n) c₁ [Y]` equals the multiplicity of
   `c₁` in `V^⊗n ⊗ Y`, and in particular `(mckayMatrix V ^ n) c trivial` is the multiplicity of `c`
   in `V^⊗n`.

## Main definitions

* `TauCeti.SimpleFDRepClasses.finrank`, `TauCeti.SimpleFDRepClasses.trivial`, and
  `TauCeti.SimpleFDRepClasses.multiplicity`: dimension, trivial class, and multiplicity of a simple
  isomorphism class in an object of `FDRep k G`.
* `TauCeti.mckayMatrix`: the matrix `(c₁, c₂) ↦ dim_k Hom_G(X, V ⊗ Y)` on `SimpleFDRepClasses k G`.

## Main results

* `FDRep.finrank_hom_tensor_self_eq_zero` and `TauCeti.mckayMatrix_apply_self_eq_zero`:
  loop-freeness for faithful two-dimensional representations of determinant `1`.
* `TauCeti.isSymm_mckayMatrix_of_equiv_dual` and `TauCeti.isSymm_mckayMatrix`: symmetry of
  `mckayMatrix V`.
* `TauCeti.finrank_eq_sum_multiplicity_mul_finrank` and `TauCeti.sum_mckayMatrix_mul_finrank`:
  dimension decomposition and the null-vector equation `M δ = (dim V) δ`.
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

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G]

/-- If `g₀ : G` commutes with `G` and `(V.ρ g₀ - c₁ • id) ∘ (V.ρ g₀ - c₂ • id) = 0` with
`c₁ ≠ 1` and `c₂ ≠ 1`, then no simple `X` admits a nonzero intertwiner `X ⟶ V ⊗ X`. -/
private theorem finrank_hom_tensor_self_eq_zero_of_central {V : FDRep k G} {g₀ : G}
    (hcomm : ∀ h : G, g₀ * h = h * g₀) {c₁ c₂ : k} (hc₁ : c₁ ≠ 1) (hc₂ : c₂ ≠ 1)
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
  have hz₁ : ((V.ρ g₀ - c₁ • LinearMap.id).rTensor X) z = (1 - c₁) • z := by
    rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_id,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz, sub_smul, one_smul]
  have hz₂ : ((V.ρ g₀ - c₂ • LinearMap.id).rTensor X) z = (1 - c₂) • z := by
    rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_id,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz, sub_smul, one_smul]
  have hzero : ((1 - c₁) * (1 - c₂)) • z = 0 := by
    rw [← smul_smul]
    calc
      (1 - c₁) • ((1 - c₂) • z) =
          ((V.ρ g₀ - c₁ • LinearMap.id).rTensor X) ((1 - c₂) • z) := by
        rw [map_smul, hz₁, smul_comm]
      _ = (((V.ρ g₀ - c₁ • LinearMap.id) ∘ₗ (V.ρ g₀ - c₂ • LinearMap.id)).rTensor X) z := by
        rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hz₂]
      _ = 0 := by rw [hann, LinearMap.rTensor_zero, LinearMap.zero_apply]
  have hz0 : z = 0 :=
    (smul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr hc₁.symm) (sub_ne_zero.mpr hc₂.symm))
  simpa [z] using hz0

/-- **Loop-freeness of the McKay graph.** For a nontrivial finite group `G` and a faithful
two-dimensional representation `V : FDRep k G` of determinant `1` over an algebraically closed
field `k` of characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. -/
theorem finrank_hom_tensor_self_eq_zero [CharZero k] [Finite G] [Nontrivial G] (V : FDRep k G)
    (hdim : Module.finrank k V = 2) (hfaithful : Function.Injective V.ρ)
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
  · -- Reducible branch: Maschke splits `V` into two `1`-dimensional subrepresentations.
    have hV_not : ¬ Representation.IsIrreducible V.ρ :=
      fun h ↦ hV (FDRep.simple_of_isIrreducible V)
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (hdim ▸ zero_lt_two)
    have hW_ex : ∃ W : Subrepresentation V.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra! hall
      exact hV_not ⟨fun W ↦ or_iff_not_imp_left.mpr (hall W)⟩
    obtain ⟨W, hW_bot, hW_top⟩ := hW_ex
    have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    have : Representation.IsSemisimpleRepresentation V.ρ :=
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule V.ρ).mpr
        inferInstance
    obtain ⟨W', hWW'⟩ := exists_isCompl W
    have hWW'_sub : IsCompl W.toSubmodule W'.toSubmodule :=
      Subrepresentation.isCompl_toSubmodule.mpr hWW'
    have hW_ne_bot : W.toSubmodule ≠ ⊥ := fun h ↦
      hW_bot (Subrepresentation.toSubmodule_injective
        (h.trans Subrepresentation.toSubmodule_bot.symm))
    have hW_lt_top : W.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr fun h ↦
      hW_top (Subrepresentation.toSubmodule_injective
        (h.trans Subrepresentation.toSubmodule_top.symm))
    have hW_pos : 0 < Module.finrank k W.toSubmodule :=
      let ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W.toSubmodule).mp hW_ne_bot
      have : Nontrivial W.toSubmodule := ⟨⟨⟨w, hw⟩, 0, Subtype.coe_ne_coe.mp hw0⟩⟩
      Module.finrank_pos
    have hW_lt : Module.finrank k W.toSubmodule < 2 := by
      simpa [finrank_top, hdim] using Submodule.finrank_lt_finrank_of_lt hW_lt_top
    have hW1 : Module.finrank k W.toSubmodule = 1 := by omega
    have hW'1 : Module.finrank k W'.toSubmodule = 1 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq W.toSubmodule W'.toSubmodule
      rw [hWW'_sub.sup_eq_top, hWW'_sub.inf_eq_bot, finrank_top, finrank_bot,
        hdim, hW1] at hsum
      omega
    let bW : Module.Basis (Fin 1) k W.toSubmodule :=
      Module.finBasisOfFinrankEq k W.toSubmodule hW1
    let bW' : Module.Basis (Fin 1) k W'.toSubmodule :=
      Module.finBasisOfFinrankEq k W'.toSubmodule hW'1
    let u₀ : V := bW 0
    let u₁ : V := bW' 0
    have hli : LinearIndependent k ![u₀, u₁] := by
      rw [Fintype.linearIndependent_iff]
      intro f hf
      rw [Fin.sum_univ_two] at hf
      dsimp at hf
      have hmem : f 0 • u₀ ∈ W.toSubmodule ⊓ W'.toSubmodule := by
        refine ⟨Submodule.smul_mem _ _ (bW 0).2, ?_⟩
        have heq : f 0 • u₀ = (-f 1) • u₁ := by
          rw [neg_smul, eq_neg_iff_add_eq_zero]
          exact hf
        rw [heq]
        exact Submodule.smul_mem _ _ (bW' 0).2
      rw [hWW'_sub.inf_eq_bot, Submodule.mem_bot] at hmem
      have hf0 : f 0 = 0 :=
        (smul_eq_zero.mp hmem).resolve_right (Subtype.coe_ne_coe.mpr (bW.ne_zero 0))
      rw [hf0, zero_smul, zero_add] at hf
      have hf1 : f 1 = 0 :=
        (smul_eq_zero.mp hf).resolve_right (Subtype.coe_ne_coe.mpr (bW'.ne_zero 0))
      exact Fin.forall_fin_two.2 ⟨hf0, hf1⟩
    let b : Module.Basis (Fin 2) k V :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
    have hb0 : b 0 = u₀ := by simp [b]
    have hb1 : b 1 = u₁ := by simp [b]
    let c₁ : G → k := fun g ↦ bW.repr (W.toRepresentation g (bW 0)) 0
    let c₂ : G → k := fun g ↦ bW'.repr (W'.toRepresentation g (bW' 0)) 0
    have hc₁_apply (g : G) : V.ρ g (b 0) = c₁ g • b 0 := by
      rw [hb0]
      have hw : W.toRepresentation g (bW 0) = c₁ g • bW 0 := by
        conv_lhs => rw [← bW.sum_repr (W.toRepresentation g (bW 0)), Fin.sum_univ_one]
      exact congrArg Subtype.val hw
    have hc₂_apply (g : G) : V.ρ g (b 1) = c₂ g • b 1 := by
      rw [hb1]
      have hw : W'.toRepresentation g (bW' 0) = c₂ g • bW' 0 := by
        conv_lhs => rw [← bW'.sum_repr (W'.toRepresentation g (bW' 0)), Fin.sum_univ_one]
      exact congrArg Subtype.val hw
    have hMat (g : G) :
        LinearMap.toMatrix b b (V.ρ g) = Matrix.diagonal ![c₁ g, c₂ g] := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      revert i
      revert j
      refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · simp [hc₁_apply]
      · simp [hc₁_apply]
      · simp [hc₂_apply]
      · simp [hc₂_apply]
    have hdet_prod (g : G) : c₁ g * c₂ g = 1 := by
      have hd := hdet g
      rw [← LinearMap.det_toMatrix b, hMat g, Matrix.det_diagonal, Fin.prod_univ_two] at hd
      exact hd
    have hcomm (g h : G) : g * h = h * g :=
      hfaithful <| b.ext <| Fin.forall_fin_two.2
        ⟨by simp [map_mul, mul_apply_eq_comp, hc₁_apply, smul_smul, mul_comm],
         by simp [map_mul, mul_apply_eq_comp, hc₂_apply, smul_smul, mul_comm]⟩
    obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
    have hne_one : ¬ (c₁ g₀ = 1 ∧ c₂ g₀ = 1) := by
      rintro ⟨h1, h2⟩
      apply hg₀
      apply hfaithful
      rw [map_one]
      refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · simp [hc₁_apply, h1]
      · simp [hc₂_apply, h2]
    have hc₁_ne : c₁ g₀ ≠ 1 := fun h1 ↦
      hne_one ⟨h1, by have := hdet_prod g₀; rw [h1, one_mul] at this; exact this⟩
    have hc₂_ne : c₂ g₀ ≠ 1 := fun h2 ↦
      hne_one ⟨by have := hdet_prod g₀; rw [h2, mul_one] at this; exact this, h2⟩
    refine finrank_hom_tensor_self_eq_zero_of_central (fun h ↦ hcomm g₀ h) hc₁_ne hc₂_ne ?_ X
    refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hc₁_apply, ← sub_smul, map_smul, sub_self, smul_zero,
        LinearMap.zero_apply]
    · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hc₂_apply, sub_self, map_zero, LinearMap.zero_apply]

end LoopFree

end FDRep

namespace TauCeti

/-! ### Dimension, trivial class, and multiplicity on `SimpleFDRepClasses` -/

namespace SimpleFDRepClasses

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The vector-space dimension of a simple isomorphism class in `FDRep k G`. -/
noncomputable def finrank (c : SimpleFDRepClasses k G) : ℕ :=
  c.lift (fun (X : FDRep k G) ↦ Module.finrank k X) fun _ _ _ _ ⟨iso⟩ ↦
    (FDRep.isoToLinearEquiv iso).finrank_eq

@[simp]
theorem finrank_mk (X : FDRep k G) [Simple X] :
    (mk X).finrank = Module.finrank k X :=
  lift_mk X

/-- Every simple isomorphism class has positive dimension. -/
theorem finrank_pos (c : SimpleFDRepClasses k G) : 0 < c.finrank := by
  induction c using ind with
  | h X hX =>
    rw [finrank_mk]
    exact (FDRep.isIrreducible_of_simple X).finrank_pos

variable (k G) in
/-- The isomorphism class of the one-dimensional trivial representation in `FDRep k G`. -/
noncomputable def trivial : SimpleFDRepClasses k G :=
  mk (FDRep.of (_root_.Representation.trivial k G k))

@[simp]
theorem finrank_trivial : (trivial k G).finrank = 1 := by
  rw [trivial, finrank_mk]
  exact Module.finrank_self k

/-- **Characterization of the trivial class.** Over any field `k` and monoid `G`, a simple object
`X : FDRep k G` represents `SimpleFDRepClasses.trivial k G` if and only if every `g : G` acts as
`1` on `X`. -/
theorem mk_eq_trivial_iff (X : FDRep k G) [Simple X] :
    mk X = trivial k G ↔ ∀ g : G, X.ρ g = 1 := by
  rw [trivial, mk_eq_mk_iff]
  constructor
  · rintro ⟨iso⟩ g
    ext x
    have h := LinearMap.congr_fun (FDRep.Iso.conj_ρ iso.symm g) x
    simpa [FDRep.of_ρ', LinearEquiv.conj_apply] using h
  · intro htriv
    have hX : _root_.Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
    have : Nontrivial X := hX.nontrivial
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
    let S : Subrepresentation X.ρ :=
      { toSubmodule := Submodule.span k {x₀}
        apply_mem_toSubmodule g v hv := by
          change X.ρ g v ∈ Submodule.span k {x₀}
          rwa [htriv g, one_apply_eq_self] }
    have hS_ne : S ≠ ⊥ := by
      intro hbot
      apply hx₀
      have hx_mem : x₀ ∈ S.toSubmodule := Submodule.mem_span_singleton_self x₀
      rwa [hbot, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hx_mem
    have hS_top : S.toSubmodule = ⊤ := by
      rw [(hX.eq_bot_or_eq_top S).resolve_left hS_ne, Subrepresentation.toSubmodule_top]
    have hdim1 : Module.finrank k X = 1 := by
      rw [← finrank_top, ← hS_top, finrank_span_singleton hx₀]
    let b : Module.Basis (Fin 1) k X := Module.finBasisOfFinrankEq k X hdim1
    let e : X ≃ₗ[k] k := b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite k k (Fin 1) ≪≫ₗ
      LinearEquiv.funUnique (Fin 1) k k
    exact ⟨e.toFDRepIso (Y := FDRep.of (_root_.Representation.trivial k G k))
      fun g x ↦ by simp [htriv g]⟩

/-- The multiplicity `dim_k Hom_G(X, W)` of a simple class `c = [X]` in `W : FDRep k G`. -/
noncomputable def multiplicity (c : SimpleFDRepClasses k G) (W : FDRep k G) : ℕ :=
  c.lift (fun X ↦ Module.finrank k (X ⟶ W)) fun _ _ _ _ ⟨iso⟩ ↦
    (Linear.homCongr k iso (Iso.refl W)).finrank_eq

@[simp]
theorem multiplicity_mk (X : FDRep k G) [Simple X] (W : FDRep k G) :
    (mk X).multiplicity W = Module.finrank k (X ⟶ W) :=
  lift_mk X

/-- `SimpleFDRepClasses.multiplicity` is invariant under isomorphism in the target object. -/
theorem multiplicity_congr (c : SimpleFDRepClasses k G) {W₁ W₂ : FDRep k G} (iso : W₁ ≅ W₂) :
    c.multiplicity W₁ = c.multiplicity W₂ := by
  induction c using ind with
  | h X hX =>
    simp only [multiplicity_mk]
    exact (Linear.homCongr k (Iso.refl X) iso).finrank_eq

/-- Over an algebraically closed field, the multiplicity of a simple class `c` in a simple `Y` is
`1` at `mk Y` and `0` elsewhere (Schur's lemma). -/
theorem multiplicity_simple [IsAlgClosed k] [DecidableEq (SimpleFDRepClasses k G)]
    (c : SimpleFDRepClasses k G) (Y : FDRep k G) [Simple Y] :
    c.multiplicity Y = if c = mk Y then 1 else 0 := by
  induction c using ind with
  | h X hX =>
    have : Simple X := hX
    rw [multiplicity_mk, FDRep.finrank_hom_simple_simple X Y]
    exact ite_congr (propext (mk_eq_mk_iff X Y).symm) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Field

end SimpleFDRepClasses

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

/-- **Symmetry of the McKay matrix** for a self-dual representation when `|G|` is invertible in
`k`. -/
theorem isSymm_mckayMatrix_of_equiv_dual [Group G] [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (_root_.Representation.dual V.ρ))) :
    (mckayMatrix V).IsSymm := by
  ext c₁ c₂
  induction c₁ using SimpleFDRepClasses.ind with
  | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [Matrix.transpose_apply, mckayMatrix_mk_mk, mckayMatrix_mk_mk]
    exact FDRep.finrank_hom_tensor_comm_of_equiv_dual he Y X

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

/-- A finite-dimensional representation `W : FDRep k G` is equivalent to the direct sum of
`m_W(i)` copies of the irreducible models `irreducibleRepresentation k i`. -/
private theorem nonempty_equiv_directSum_irreducibleRepresentation (W : FDRep k G) :
    Nonempty (_root_.Representation.Equiv W.ρ
      (_root_.Representation.directSum
        fun s : Σ i : Fin (Nat.card (ConjClasses G)),
            Fin (_root_.Representation.intrinsicMultiplicity W.ρ i) ↦
          irreducibleRepresentation k s.1)) := by
  rw [_root_.Representation.nonempty_equiv_iff_intrinsicMultiplicity_eq]
  ext j
  rw [_root_.Representation.intrinsicMultiplicity_directSum, Fintype.sum_sigma]
  simp

/-- `SimpleFDRepClasses.multiplicity` at row `i` of `equivFinCardConjClasses` agrees with
`Representation.intrinsicMultiplicity`. -/
theorem SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm (W : FDRep k G)
    (i : Fin (Nat.card (ConjClasses G))) :
    ((SimpleFDRepClasses.equivFinCardConjClasses k G).symm i).multiplicity W =
      _root_.Representation.intrinsicMultiplicity W.ρ i := by
  rw [SimpleFDRepClasses.equivFinCardConjClasses_symm_apply, SimpleFDRepClasses.multiplicity_mk,
    FDRep.intrinsicMultiplicity_ρ_eq_finrank_hom]

/-- **Dimension decomposition into simple classes.** Every `W : FDRep k G` has dimension
`∑ c, c.multiplicity W * c.finrank`. -/
theorem finrank_eq_sum_multiplicity_mul_finrank [Fintype (SimpleFDRepClasses k G)]
    (W : FDRep k G) :
    Module.finrank k W = ∑ c : SimpleFDRepClasses k G, c.multiplicity W * c.finrank := by
  obtain ⟨e⟩ := nonempty_equiv_directSum_irreducibleRepresentation W
  have hdim : Module.finrank k W =
      ∑ i : Fin (Nat.card (ConjClasses G)),
        _root_.Representation.intrinsicMultiplicity W.ρ i *
          Module.finrank k (FDRep.of (irreducibleRepresentation k i) : FDRep k G) := by
    rw [e.toLinearEquiv.finrank_eq,
      (DirectSum.linearEquivFunOnFintype k _ _).finrank_eq, Module.finrank_pi_fintype k,
      Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine (Finset.sum_congr rfl fun _ _ ↦
      (rfl : _ = Module.finrank k (FDRep.of (irreducibleRepresentation k i) : FDRep k G))).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hdim]
  refine Finset.sum_equiv (SimpleFDRepClasses.equivFinCardConjClasses k G).symm
    (s := univ) (t := univ) (fun _ ↦ by simp) fun i _ ↦ ?_
  rw [SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm,
    SimpleFDRepClasses.equivFinCardConjClasses_symm_apply, SimpleFDRepClasses.finrank_mk]

/-- Column sum of `mckayMatrix V` against the irreducible dimensions:
`∑ c₁, mckayMatrix V c₁ c₂ * c₁.finrank = dim V * c₂.finrank`. -/
theorem sum_mckayMatrix_mul_finrank_left [Fintype (SimpleFDRepClasses k G)] (V : FDRep k G)
    (c₂ : SimpleFDRepClasses k G) :
    ∑ c₁ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₁.finrank =
      Module.finrank k V * c₂.finrank := by
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    simp_rw [mckayMatrix_apply_mk, SimpleFDRepClasses.finrank_mk]
    rw [← finrank_eq_sum_multiplicity_mul_finrank (V ⊗ Y)]
    change Module.finrank k (V ⊗[k] Y) = Module.finrank k V * Module.finrank k Y
    exact Module.finrank_tensorProduct

/-- **Null-vector equation `M δ = (dim V) δ`** for a representation whose McKay matrix is
symmetric. -/
theorem sum_mckayMatrix_mul_finrank [Fintype (SimpleFDRepClasses k G)] {V : FDRep k G}
    (hSymm : (mckayMatrix V).IsSymm) (c₁ : SimpleFDRepClasses k G) :
    ∑ c₂ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₂.finrank =
      Module.finrank k V * c₁.finrank := by
  simp_rw [show ∀ c₂, mckayMatrix V c₁ c₂ = mckayMatrix V c₂ c₁ from fun c₂ ↦ hSymm.apply c₂ c₁]
  exact sum_mckayMatrix_mul_finrank_left V c₁

/-- Tensoring on the left distributes over `Representation.directSum`. -/
private noncomputable def tprodDirectSumEquiv {V₀ : Type*} [AddCommGroup V₀] [Module k V₀]
    (ρ : _root_.Representation k G V₀) {ι : Type*} [DecidableEq ι] {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (σ : ∀ i, _root_.Representation k G (W i)) :
    _root_.Representation.Equiv (ρ.tprod (_root_.Representation.directSum σ))
      (_root_.Representation.directSum fun i ↦ ρ.tprod (σ i)) :=
  .mk (TensorProduct.directSumRight k k V₀ W) fun g ↦
    TensorProduct.ext' fun v w ↦ by
      induction w using DirectSum.induction_on with
      | zero => simp
      | of i x =>
        rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          _root_.Representation.tprod_apply, TensorProduct.map_tmul,
          _root_.Representation.directSum_apply, ← DirectSum.lof_eq_of k,
          DirectSum.lmap_lof, TensorProduct.directSumRight_tmul_lof,
          TensorProduct.directSumRight_tmul_lof, _root_.Representation.directSum_apply,
          DirectSum.lmap_lof, _root_.Representation.tprod_apply, TensorProduct.map_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- **Multiplicity in `V ⊗ W` expands by matrix-vector multiplication with `mckayMatrix V`.** -/
theorem multiplicity_tensor_eq_sum [Fintype (SimpleFDRepClasses k G)] (V W : FDRep k G)
    (c₁ : SimpleFDRepClasses k G) :
    c₁.multiplicity (V ⊗ W) =
      ∑ c₂ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₂.multiplicity W := by
  classical
  obtain ⟨eW⟩ := nonempty_equiv_directSum_irreducibleRepresentation W
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
          _root_.Representation.tprod V.ρ (irreducibleRepresentation k s.1)) := by
    refine (_root_.Representation.Equiv.mk (LinearEquiv.refl k _) fun g ↦ ?_).trans
      (((_root_.Representation.Equiv.refl V.ρ).tprod eW).trans (tprodDirectSumEquiv V.ρ _))
    rw [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id, FDRep.tensor_ρ,
      _root_.Representation.tprod_apply]
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
  congr 1

/-- `V.tensorPower 0` is isomorphic in `FDRep k G` to the monoidal unit `𝟙_ (FDRep k G)`. -/
private noncomputable def tensorPowerZeroIsoTensorUnit (V : FDRep k G) :
    V.tensorPower 0 ≅ 𝟙_ (FDRep k G) :=
  eqToIso (FDRep.tensorPower_def V 0) ≪≫
    (PiTensorProduct.isEmptyEquiv (Fin 0)).toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ', FDRep.tensorUnit_ρ, _root_.Representation.tensorPower_zero_apply,
        LinearMap.id_apply, LinearMap.id_apply]

/-- The bundled trivial representation on `k` is isomorphic to `𝟙_ (FDRep k G)`. -/
private noncomputable def trivialIsoTensorUnit :
    FDRep.of (_root_.Representation.trivial k G k) ≅ 𝟙_ (FDRep k G) :=
  (LinearEquiv.refl k k).toFDRepIso fun g x ↦ by
    rw [FDRep.of_ρ', FDRep.tensorUnit_ρ, _root_.Representation.trivial_apply, LinearMap.id_apply]

/-- `V.tensorPower (n + 1)` is isomorphic in `FDRep k G` to `V ⊗ V.tensorPower n`. -/
private noncomputable def tensorPowerSuccIso (V : FDRep k G) (n : ℕ) :
    V.tensorPower (n + 1) ≅ (V ⊗ V.tensorPower n : FDRep k G) := by
  have e1 : _root_.Representation.Equiv V.ρ (_root_.Representation.tensorPower V.ρ 1) :=
    .mk (TauCeti.TensorPower.oneEquiv k V).symm fun g ↦ by
      simpa only [_root_.Representation.tensorPower_apply] using
        TauCeti.TensorPower.oneEquiv_symm_comp (V.ρ g)
  have e2 : _root_.Representation.Equiv
      ((V ⊗ FDRep.of (_root_.Representation.tensorPower V.ρ n) : FDRep k G)).ρ
      (_root_.Representation.tensorPower V.ρ (1 + n)) := by
    refine (_root_.Representation.Equiv.mk (LinearEquiv.refl k _) fun g ↦ ?_).trans
      ((e1.tprod (_root_.Representation.Equiv.refl _)).trans
        (_root_.Representation.tensorPowerAddEquiv V.ρ 1 n))
    rw [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id, FDRep.tensor_ρ,
      FDRep.of_ρ', _root_.Representation.tprod_apply]
  have e3 : _root_.Representation.Equiv
      (_root_.Representation.tensorPower V.ρ (1 + n))
      (_root_.Representation.tensorPower V.ρ (n + 1)) :=
    Nat.add_comm 1 n ▸ _root_.Representation.Equiv.refl _
  exact eqToIso (FDRep.tensorPower_def V (n + 1)) ≪≫
    ((e2.trans e3).toLinearEquiv.toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ']
      exact LinearMap.congr_fun ((e2.trans e3).isIntertwining' g) x).symm ≪≫
    whiskerLeftIso V (eqToIso (FDRep.tensorPower_def V n)).symm

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
      c₁.multiplicity_congr (whiskerRightIso (tensorPowerZeroIsoTensorUnit V) Y ≪≫ λ_ Y),
      c₁.multiplicity_simple Y]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [← multiplicity_tensor_eq_sum V (V.tensorPower n ⊗ Y) c₁]
    exact c₁.multiplicity_congr
      ((whiskerRightIso (tensorPowerSuccIso V n) Y ≪≫ α_ V (V.tensorPower n) Y).symm)

/-- **Entries at the trivial column of `mckayMatrix V ^ n` count multiplicities in `V^⊗n`.** -/
theorem mckayMatrix_pow_apply_trivial [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ)
    (c : SimpleFDRepClasses k G) :
    (mckayMatrix V ^ n) c (SimpleFDRepClasses.trivial k G) = c.multiplicity (V.tensorPower n) := by
  rw [SimpleFDRepClasses.trivial, mckayMatrix_pow_apply]
  exact c.multiplicity_congr
    (whiskerLeftIso (V.tensorPower n) trivialIsoTensorUnit ≪≫ ρ_ (V.tensorPower n))

end Semisimple

end McKayMatrix

end TauCeti

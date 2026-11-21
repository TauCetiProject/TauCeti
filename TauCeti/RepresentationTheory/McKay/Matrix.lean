/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Multiplicity
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.Tensor.Power
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.LinearAlgebra.Determinant.FiniteOrder
import TauCeti.RepresentationTheory.CharacterTable.Degree
import TauCeti.RepresentationTheory.CharacterTable.Regrouping
import TauCeti.RepresentationTheory.Intertwining.DirectSum
import TauCeti.RepresentationTheory.InvariantForm.Determinant
import TauCeti.RepresentationTheory.Irreducible

/-!
# The McKay matrix and tensor-power multiplicities

For an object `V` of `FDRep k G`, the **McKay matrix** `TauCeti.mckayMatrix V` is the matrix indexed
by `TauCeti.SimpleFDRepClasses k G` whose `(c₁, c₂)` entry is `dim_k Hom_G(X, V ⊗ Y)` for
representatives `c₁ = [X]` and `c₂ = [Y]`. This file establishes its loop-freeness on faithful
two-dimensional representations of determinant `1` over an algebraically closed field of
characteristic zero, its duality `(mckayMatrix V)ᵀ = mckayMatrix (ᘁV)` and symmetry under
self-duality, the dimension null-vector equation `M δ = (dim V) δ`, and the identification of
`(mckayMatrix V ^ n) c₁ [Y]` with the multiplicity of `c₁` in `V^⊗n ⊗ Y`.

## Main definitions and results

* `TauCeti.mckayMatrix`: the matrix `(c₁, c₂) ↦ dim_k Hom_G(X, V ⊗ Y)` on `SimpleFDRepClasses k G`,
  with `TauCeti.mckayMatrix_apply_trivial`, `TauCeti.mckayMatrix_zero`,
  `TauCeti.mckayMatrix_biprod`, `TauCeti.mckayMatrix_tensorUnit`, and `TauCeti.mckayMatrix_tensor`.
* `FDRep.finrank_hom_tensor_self_eq_zero` and `TauCeti.mckayMatrix_apply_self_eq_zero`:
  loop-freeness for faithful two-dimensional representations of determinant `1`.
* `TauCeti.mckayMatrix_transpose`, `TauCeti.isSymm_mckayMatrix_of_equiv_dual`, and
  `TauCeti.isSymm_mckayMatrix_of_finrank_eq_two`: transpose via `ᘁV` and symmetry.
* `TauCeti.sum_mckayMatrix_mul_finrank_left` and `TauCeti.sum_mckayMatrix_mul_finrank`:
  column-sum identity and null-vector equation `M δ = (dim V) δ`.
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

namespace FDRep

section LoopFree

variable {k : Type u} {G : Type v} [Field k] [Group G]

private theorem exists_central_annihilator_of_not_simple [Nontrivial G]
    [NeZero (Nat.card G : k)] {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hfaithful : Function.Injective V.ρ) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1)
    (hV : ¬ Simple V) :
    ∃ (g₀ : G) (c₁ c₂ : k), (∀ h : G, g₀ * h = h * g₀) ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧
      (V.ρ g₀ - c₁ • LinearMap.id) ∘ₗ (V.ρ g₀ - c₂ • LinearMap.id) = 0 := by
  -- Split `V.ρ` by Maschke into two complementary invariant lines on which `G` acts by scalars.
  obtain ⟨W, W', hWW', hW1, hW'1⟩ :=
    Representation.exists_isCompl_finrank_eq_one_of_not_isIrreducible hdim
      (mt (FDRep.simple_iff_isIrreducible V).mpr hV)
  let e := Subrepresentation.equivProdOfIsCompl hWW'
  choose c₁ hc₁ using fun g : G ↦
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW1 (W.toRepresentation g)).exists
  choose c₂ hc₂ using fun g : G ↦
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW'1 (W'.toRepresentation g)).exists
  let eL : V ≃ₗ[k] W.toSubmodule × W'.toSubmodule := e.toLinearEquiv
  have he_apply (g : G) (v : V) : eL (V.ρ g v) = (c₁ g • (eL v).1, c₂ g • (eL v).2) := by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    exact Prod.ext (by simpa [eL, hc₁ g] using congrArg Prod.fst h)
      (by simpa [eL, hc₂ g] using congrArg Prod.snd h)
  -- Read `det (V.ρ g) = 1` across `V ≃ W × W'` to get `c₁ g * c₂ g = 1`, and deduce `G` is abelian
  -- since `V.ρ` embeds `G` into diagonal matrices.
  have hconj (g : G) :
      (eL : V →ₗ[k] W.toSubmodule × W'.toSubmodule) ∘ₗ V.ρ g ∘ₗ
          (eL.symm : W.toSubmodule × W'.toSubmodule →ₗ[k] V) =
        LinearMap.prodMap (c₁ g • LinearMap.id) (c₂ g • LinearMap.id) :=
    LinearMap.ext fun p ↦ Prod.ext (by simp [he_apply]) (by simp [he_apply])
  have hdet_prod (g : G) : c₁ g * c₂ g = 1 := by
    have hd : LinearMap.det ((eL : V →ₗ[k] W.toSubmodule × W'.toSubmodule) ∘ₗ V.ρ g ∘ₗ
        (eL.symm : W.toSubmodule × W'.toSubmodule →ₗ[k] V)) = 1 := by
      rw [LinearMap.det_conj, hdet g]
    simpa [hconj g, LinearMap.det_prodMap, hW1, hW'1] using hd
  have hcomm (g h : G) : g * h = h * g :=
    hfaithful <| LinearMap.ext fun v ↦ eL.injective <| by
      simp [map_mul, mul_apply_eq_comp, he_apply, smul_smul, mul_comm]
  -- Any `g₀ ≠ 1` is central with inverse eigenvalues `c₁ g₀, c₂ g₀ ≠ 1` annihilating `V.ρ g₀`.
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
  have hne_one : ¬ (c₁ g₀ = 1 ∧ c₂ g₀ = 1) := fun ⟨h1, h2⟩ ↦
    hg₀ <| hfaithful <| by
      rw [map_one]; exact LinearMap.ext fun v ↦ eL.injective (by simp [he_apply, h1, h2])
  have hc₁_ne : c₁ g₀ ≠ 1 := fun h1 ↦ hne_one ⟨h1, by simpa [h1] using hdet_prod g₀⟩
  have hc₂_ne : c₂ g₀ ≠ 1 := fun h2 ↦ hne_one ⟨by simpa [h2] using hdet_prod g₀, h2⟩
  refine ⟨g₀, c₁ g₀, c₂ g₀, fun h ↦ hcomm g₀ h, hc₁_ne, hc₂_ne, LinearMap.ext fun v ↦ ?_⟩
  apply eL.injective
  ext <;> simp [he_apply, smul_sub, smul_smul, mul_comm]

/-- **Loop-freeness of the McKay graph.** For a nontrivial finite group `G` and a faithful
two-dimensional representation `V : FDRep k G` of determinant `1` over an algebraically closed
field `k` of characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. -/
theorem finrank_hom_tensor_self_eq_zero [IsAlgClosed k] [CharZero k] [Finite G] [Nontrivial G]
    (V : FDRep k G) (hdim : Module.finrank k V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  by_cases hV : Simple V
  · have : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' 2 (hdim ▸ FDRep.finrank_dvd_card V)
    have hg₀_ne : g₀ ≠ 1 := fun h1 ↦ by simp [h1] at hg₀
    have hg₀_sq : V.ρ g₀ * V.ρ g₀ = 1 := by
      rw [← map_mul, ← sq, ← hg₀, pow_orderOf_eq_one, map_one]
    have hVg₀ : V.ρ g₀ = -1 :=
      (LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one two_ne_zero hdim hg₀_sq
        (hdet g₀)).resolve_left fun h1 ↦ hg₀_ne (hfaithful (h1.trans (map_one V.ρ).symm))
    have hcomm (h : G) : g₀ * h = h * g₀ := hfaithful <| by
      rw [map_mul, map_mul, hVg₀, neg_one_mul, mul_neg_one]
    have hneg1 : (-1 : k) ≠ 1 := fun h ↦ (two_ne_zero : (2 : k) ≠ 0) <| by
      simpa [one_add_one_eq_two] using (congrArg (· + (1 : k)) h).symm
    exact finrank_hom_tensor_self_eq_zero_of_central hcomm hneg1 hneg1 (by ext; simp [hVg₀]) X
  · have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨g₀, c₁, c₂, hcomm, hc₁, hc₂, hann⟩ :=
      exists_central_annihilator_of_not_simple hdim hfaithful hdet hV
    exact finrank_hom_tensor_self_eq_zero_of_central hcomm hc₁ hc₂ hann X

end LoopFree

end FDRep

namespace TauCeti

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

/-- Entry `(c, trivial)` of `mckayMatrix V` is the multiplicity `c.multiplicity V`. -/
@[simp]
theorem mckayMatrix_apply_trivial [Monoid G] (V : FDRep k G) (c : SimpleFDRepClasses k G) :
    mckayMatrix V c (SimpleFDRepClasses.trivial k G) = c.multiplicity V := by
  rw [← SimpleFDRepClasses.mk_tensorUnit, mckayMatrix_apply_mk]
  exact c.multiplicity_congr (ρ_ V)

/-- Isomorphic objects in `FDRep k G` have the same McKay matrix. -/
theorem mckayMatrix_congr [Monoid G] {V₁ V₂ : FDRep k G} (iso : V₁ ≅ V₂) :
    mckayMatrix V₁ = mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, mckayMatrix_apply_mk]
    exact c₁.multiplicity_congr (whiskerRightIso iso Y)

open scoped ZeroObject in
/-- **Zero law for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_zero [Monoid G] : mckayMatrix (0 : FDRep k G) = 0 := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, Matrix.zero_apply]
    have hzero : Limits.IsZero ((0 : FDRep k G) ⊗ Y) :=
      (CategoryTheory.MonoidalCategory.tensorRight Y).map_isZero
        (Limits.isZero_zero (FDRep k G))
    rw [c₁.multiplicity_congr hzero.isoZero, SimpleFDRepClasses.multiplicity_zero]

/-- **Additivity on biproducts for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_biprod [Monoid G] (V₁ V₂ : FDRep k G) :
    mckayMatrix (V₁ ⊞ V₂) = mckayMatrix V₁ + mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    let _ := Limits.preservesBinaryBiproducts_of_preservesBiproducts
      (CategoryTheory.MonoidalCategory.tensorRight Y)
    rw [mckayMatrix_apply_mk, Matrix.add_apply, mckayMatrix_apply_mk, mckayMatrix_apply_mk]
    exact (c₁.multiplicity_congr
      ((CategoryTheory.MonoidalCategory.tensorRight Y).mapBiprod V₁ V₂)).trans
      (c₁.multiplicity_biprod (V₁ ⊗ Y) (V₂ ⊗ Y))

/-- **Identity law for the McKay matrix** over an algebraically closed field. -/
@[simp]
theorem mckayMatrix_tensorUnit [IsAlgClosed k] [Monoid G] [DecidableEq (SimpleFDRepClasses k G)] :
    mckayMatrix (𝟙_ (FDRep k G)) = 1 := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, c₁.multiplicity_congr (λ_ Y), c₁.multiplicity_simple Y,
      Matrix.one_apply]

/-- **Transpose of the McKay matrix.** When `|G|` is invertible in `k`, `(mckayMatrix V)ᵀ` is the
McKay matrix of the categorical left dual `ᘁV`. -/
@[simp]
theorem mckayMatrix_transpose [Group G] [Invertible (Nat.card G : k)] (V : FDRep k G) :
    (mckayMatrix V).transpose = mckayMatrix (ᘁV) := by
  ext c₁ c₂
  induction c₁ using SimpleFDRepClasses.ind with | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with | h Y hY =>
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
theorem isSymm_mckayMatrix_of_finrank_eq_two [Group G] [Invertible (Nat.card G : k)] {V : FDRep k G}
    (hdim : Module.finrank k V = 2) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    (mckayMatrix V).IsSymm :=
  isSymm_mckayMatrix_of_equiv_dual
    (_root_.Representation.nonempty_equiv_dual_of_finrank_eq_two V.ρ hdim hdet)

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
    rw [mckayMatrix_mk_mk]; exact FDRep.finrank_hom_tensor_self_eq_zero V hdim hfaithful hdet X

section Semisimple

variable [IsAlgClosed k] [Group G] [Invertible (Nat.card G : k)]

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
  have hentry (c₂ : SimpleFDRepClasses k G) : mckayMatrix V c₁ c₂ = mckayMatrix (ᘁV) c₂ c₁ := by
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
    hc₁, SimpleFDRepClasses.multiplicity_equivFinCardConjClasses_symm,
    _root_.Representation.intrinsicMultiplicity_congr
      (FDRep.tensorEquivTprod V (FDRep.of (irreducibleRepresentation k i))),
    FDRep.of_ρ', mul_comm]

/-- **Multiplicativity on tensor products for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_tensor [Fintype (SimpleFDRepClasses k G)] (V W : FDRep k G) :
    mckayMatrix (V ⊗ W) = mckayMatrix V * mckayMatrix W := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, c₁.multiplicity_congr (α_ V W Y),
      multiplicity_tensor_eq_sum V (W ⊗ Y) c₁, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c₃ _ ↦ ?_
    rw [mckayMatrix_apply_mk]

/-- **Powers of the McKay matrix count tensor-power multiplicities.** -/
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

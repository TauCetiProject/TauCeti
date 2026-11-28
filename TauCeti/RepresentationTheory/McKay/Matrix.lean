/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import TauCeti.CategoryTheory.Action.EssentiallySmall
public import TauCeti.CategoryTheory.Semisimple.GrothendieckRing
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.FDRep.Rigid
public import TauCeti.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RepresentationTheory.Tensor.Power
import TauCeti.CategoryTheory.Action.Monoidal
import TauCeti.LinearAlgebra.Matrix.Connected
import TauCeti.RepresentationTheory.CharacterTable.IrreducibleClassification
import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
import TauCeti.RepresentationTheory.FDRep.Semisimple
import TauCeti.RepresentationTheory.FDRep.TensorHomVanishing
import TauCeti.RepresentationTheory.InvariantForm.Determinant

/-!
# The McKay matrix and tensor-power multiplicities

For an object `V` of `FDRep k G`, the **McKay matrix** `FDRep.mckayMatrix V` (`V.mckayMatrix`) is
the matrix indexed by `TauCeti.SimpleClasses (FDRep k G)` whose `(c₁, c₂)` entry is
`dim_k Hom_G(X, V ⊗ Y)` for representatives `c₁ = [X]` and `c₂ = [Y]`; under split semisimplicity
(for instance, for a finite group `G` over an algebraically closed field `k` in which `|G|` is
invertible), this is the multiplicity of `c₁` in `V ⊗ Y`. This file establishes its loop-freeness
for a nontrivial finite group `G` on faithful two-dimensional representations of determinant `1`
over an algebraically closed field of characteristic zero, its duality
`(V.mckayMatrix)ᵀ = (ᘁV).mckayMatrix` and symmetry under self-duality, its identification with
`(TauCeti.fusionMatrix k (SimpleClasses.classOf V))ᵀ` and with left multiplication by
`SplitK0.of V` on `TauCeti.SplitK0 (FDRep k G)`, the column-sum identity and dimension eigenvector
equations `M *ᵥ δ = (dim V) • δ` and `δ ᵥ* M = (dim V) • δ` (for finite groups over an
algebraically closed field in which the group order `|G|` is invertible), the identification
`(V.tensorPower n).mckayMatrix = V.mckayMatrix ^ n` with its entry formulas, and reachability to
the trivial class for faithful complex representations.

## Main definitions and results

* `FDRep.mckayMatrix`: the matrix `(c₁, c₂) ↦ dim_k Hom_G(X, V ⊗ Y)` on
  `SimpleClasses (FDRep k G)`, with `FDRep.mckayMatrix_apply_trivial`, `FDRep.mckayMatrix_zero`,
  `FDRep.mckayMatrix_biprod`, `FDRep.mckayMatrix_tensorUnit`, `FDRep.mckayMatrix_tensor`, and
  `FDRep.mckayMatrix_res_apply`.
* `FDRep.mckayMatrix_apply_self_eq_zero`: loop-freeness for faithful two-dimensional
  representations of determinant `1` of a nontrivial finite group.
* `FDRep.mckayMatrix_transpose`, `FDRep.isSymm_mckayMatrix_of_equiv_dual`, and
  `FDRep.isSymm_mckayMatrix_of_finrank_eq_two_of_det_eq_one`: transpose via `ᘁV` and symmetry.
* `FDRep.mckayMatrix_eq_transpose_fusionMatrix`: `V.mckayMatrix` equals
  `(fusionMatrix k (SimpleClasses.classOf V))ᵀ` for simple `V`.
* `FDRep.mckayMatrix_map_natCast_eq_leftMulMatrix`: the integer-cast `V.mckayMatrix` equals
  `Algebra.leftMulMatrix` by `SplitK0.of V` in `SplitK0.simpleBasis (FDRep k G)` for any `V`.
* `FDRep.sum_mckayMatrix_mul_finrank_left`, `FDRep.sum_mckayMatrix_mul_finrank`,
  `FDRep.finrank_vecMul_mckayMatrix`, and `FDRep.mckayMatrix_mulVec_finrank`: column-sum identity
  and dimension eigenvector equation `M *ᵥ δ = (dim V) • δ` (so `δ` is a null vector of
  `(dim V) I - M`) for finite groups over an algebraically closed field in which the group order
  `|G|` is invertible.
* `FDRep.mckayMatrix_tensorPower`, `FDRep.mckayMatrix_pow_apply_classOf`, and
  `FDRep.mckayMatrix_pow_apply_trivial`: under split semisimplicity, powers of `V.mckayMatrix`
  compute tensor-power multiplicities.
* `FDRep.reflTransGen_mckayMatrix_trivial`: reachability to the trivial class for faithful
  complex representations.

## References

* J. McKay, *Graphs, singularities, and finite groups*, Proc. Symp. Pure Math. **37** (1980),
  183–186.
* R. Steinberg, *Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*, Pacific J.
  Math. **118** (1985), 587–598.
-/

public section

open CategoryTheory MonoidalCategory Finset
open scoped Matrix TensorProduct

universe u v w

namespace FDRep

section McKayMatrix

open TauCeti

variable {k : Type u} {G : Type v} [Field k]

/-- **The McKay matrix** of `V : FDRep k G`, indexed by `SimpleClasses (FDRep k G)`, with
`(c₁, c₂)` entry `dim_k Hom_G(X, V ⊗ Y)` for representatives `c₁ = [X]` and `c₂ = [Y]` (the
multiplicity of `c₁` in `V ⊗ Y` under split semisimplicity). -/
noncomputable def mckayMatrix [Monoid G] (V : FDRep k G) :
    Matrix (SimpleClasses (FDRep k G)) (SimpleClasses (FDRep k G)) ℕ :=
  fun c₁ c₂ ↦ c₁.finrankHom (V ⊗ c₂.repr)

@[simp]
theorem mckayMatrix_apply_classOf [Monoid G] (V : FDRep k G) (c₁ : SimpleClasses (FDRep k G))
    (Y : FDRep k G) [Simple Y] :
    mckayMatrix V c₁ (SimpleClasses.classOf Y) = c₁.finrankHom (V ⊗ Y) :=
  c₁.finrankHom_congr (whiskerLeftIso V (SimpleClasses.classOfReprIso Y))

/-- Entry `(classOf X, classOf Y)` of `mckayMatrix V` is `dim_k Hom_G(X, V ⊗ Y)`. -/
theorem mckayMatrix_classOf_classOf [Monoid G] (V X Y : FDRep k G) [Simple X] [Simple Y] :
    mckayMatrix V (SimpleClasses.classOf X) (SimpleClasses.classOf Y) =
      Module.finrank k (X ⟶ V ⊗ Y) := by
  rw [mckayMatrix_apply_classOf, SimpleClasses.finrankHom_classOf]

/-- Entry `(c, trivial)` of `mckayMatrix V` is `c.finrankHom V` (the multiplicity of `c` in `V`
under split semisimplicity). -/
@[simp]
theorem mckayMatrix_apply_trivial [Monoid G] (V : FDRep k G) (c : SimpleClasses (FDRep k G)) :
    mckayMatrix V c (SimpleClasses.trivial k G) = c.finrankHom V := by
  rw [← SimpleClasses.classOf_tensorUnit, mckayMatrix_apply_classOf]
  exact c.finrankHom_congr (ρ_ V)

/-- Isomorphic objects in `FDRep k G` have the same McKay matrix. -/
theorem mckayMatrix_congr [Monoid G] {V₁ V₂ : FDRep k G} (iso : V₁ ≅ V₂) :
    mckayMatrix V₁ = mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    rw [mckayMatrix_apply_classOf, mckayMatrix_apply_classOf]
    exact c₁.finrankHom_congr (whiskerRightIso iso Y)

/-- **Naturality of the McKay matrix under a monoid isomorphism.** Restricting `V : FDRep k G₂`
along `φ : G₁ ≃* G₂` pulls back `mckayMatrix V` along
`SimpleClasses.equiv (Action.resEquiv (FGModuleCat k) φ)`. -/
@[simp]
theorem mckayMatrix_res_apply {k : Type u} {G₁ : Type v} {G₂ : Type w} [Field k]
    [Monoid G₁] [Monoid G₂] (φ : G₁ ≃* G₂) (V : FDRep k G₂)
    (c₁ c₂ : SimpleClasses (FDRep k G₂)) :
    mckayMatrix ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj V)
        (SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ) c₁)
        (SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ) c₂) =
      mckayMatrix V c₁ c₂ := by
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    rw [SimpleClasses.equiv_apply_classOf, mckayMatrix_apply_classOf, mckayMatrix_apply_classOf]
    change (SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ) c₁).finrankHom
        ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj V ⊗
          (Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj Y) = c₁.finrankHom (V ⊗ Y)
    rw [(SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ) c₁).finrankHom_congr
        (Functor.Monoidal.μIso (Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)) V Y),
      SimpleClasses.finrankHom_equiv_actionResEquiv]

open scoped ZeroObject in
/-- **Zero law for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_zero [Monoid G] : mckayMatrix (0 : FDRep k G) = 0 := by
  ext c₁ c₂
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    rw [mckayMatrix_apply_classOf, Matrix.zero_apply]
    have hzero : Limits.IsZero ((0 : FDRep k G) ⊗ Y) :=
      (CategoryTheory.MonoidalCategory.tensorRight Y).map_isZero
        (Limits.isZero_zero (FDRep k G))
    rw [c₁.finrankHom_congr hzero.isoZero, SimpleClasses.finrankHom_zero]

/-- **Additivity on biproducts for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_biprod [Monoid G] (V₁ V₂ : FDRep k G) :
    mckayMatrix (V₁ ⊞ V₂) = mckayMatrix V₁ + mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    let _ := Limits.preservesBinaryBiproducts_of_preservesBiproducts
      (CategoryTheory.MonoidalCategory.tensorRight Y)
    rw [mckayMatrix_apply_classOf, Matrix.add_apply, mckayMatrix_apply_classOf,
      mckayMatrix_apply_classOf]
    exact (c₁.finrankHom_congr
      ((CategoryTheory.MonoidalCategory.tensorRight Y).mapBiprod V₁ V₂)).trans
      (c₁.finrankHom_biprod (V₁ ⊗ Y) (V₂ ⊗ Y))

/-- **Identity law for the McKay matrix** over an algebraically closed field. -/
@[simp]
theorem mckayMatrix_tensorUnit [IsAlgClosed k] [Monoid G]
    [DecidableEq (SimpleClasses (FDRep k G))] :
    mckayMatrix (𝟙_ (FDRep k G)) = 1 := by
  ext c₁ c₂
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    rw [mckayMatrix_apply_classOf, c₁.finrankHom_congr (λ_ Y), c₁.finrankHom_simple Y,
      Matrix.one_apply]

/-- **Transpose of the McKay matrix.** When `|G|` is invertible in `k`, `(mckayMatrix V)ᵀ` is the
McKay matrix of the categorical left dual `ᘁV`. -/
@[simp]
theorem mckayMatrix_transpose [Group G] [Invertible (Nat.card G : k)] (V : FDRep k G) :
    (mckayMatrix V).transpose = mckayMatrix (ᘁV : FDRep k G) := by
  ext c₁ c₂
  induction c₁ using SimpleClasses.ind with | h X =>
  induction c₂ using SimpleClasses.ind with | h Y =>
    rw [Matrix.transpose_apply, mckayMatrix_classOf_classOf, mckayMatrix_classOf_classOf]
    exact FDRep.finrank_hom_tensor_leftDual V Y X

/-- **Bridge between the McKay matrix and the fusion matrix.** When `|G|` is invertible in `k`,
for any simple object `V : FDRep k G`, `mckayMatrix V` equals the transpose of
`TauCeti.fusionMatrix`. -/
theorem mckayMatrix_eq_transpose_fusionMatrix [Group G] [Invertible (Nat.card G : k)]
    (V : FDRep k G) [Simple V] :
    mckayMatrix V = (fusionMatrix k (SimpleClasses.classOf V)).transpose := by
  ext S T
  simp only [Matrix.transpose_apply, fusionMatrix_apply, fusionCoeff_def]
  rw [← SimpleClasses.classOf_repr S, ← SimpleClasses.classOf_repr T, mckayMatrix_classOf_classOf,
    SimpleClasses.classOf_repr S, SimpleClasses.classOf_repr T, FDRep.finrank_hom_comm]
  exact (Linear.homCongr k (whiskerRightIso (SimpleClasses.classOfReprIso V).symm T.repr)
    (Iso.refl S.repr)).finrank_eq

/-- **Bridge between the McKay matrix and the representation ring.** Over an algebraically closed
field `k` in which `|G|` is nonzero, for any `V : FDRep k G` (not necessarily simple), the
integer-cast McKay matrix gives the matrix of left multiplication by `SplitK0.of V` in
`SplitK0.simpleBasis (FDRep k G)`. -/
theorem mckayMatrix_map_natCast_eq_leftMulMatrix [IsAlgClosed k] [Group G]
    [NeZero (Nat.card G : k)] [Fintype (SimpleClasses (FDRep k G))]
    [DecidableEq (SimpleClasses (FDRep k G))] (V : FDRep k G) :
    (mckayMatrix V).map (Nat.cast : ℕ → ℤ) =
      Algebra.leftMulMatrix (SplitK0.simpleBasis (FDRep k G)) (SplitK0.of V) := by
  ext S T
  simp only [Matrix.map_apply, mckayMatrix, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← SimpleClasses.classOf_repr S, SimpleClasses.finrankHom_classOf,
    finrank_hom_simple_eq_simpleMultiplicities k S.repr (V ⊗ T.repr),
    SimpleClasses.classOf_repr S]
  simp

/-- **Symmetry of the McKay matrix** for a self-dual representation when `|G|` is invertible in
`k`. -/
theorem isSymm_mckayMatrix_of_equiv_dual [Group G] [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (_root_.Representation.dual V.ρ))) :
    (mckayMatrix V).IsSymm := by
  obtain ⟨e⟩ := he
  rw [Matrix.IsSymm, mckayMatrix_transpose]
  exact mckayMatrix_congr (isoLeftDualOfEquivDual e).symm

/-- **Symmetry of the McKay matrix** for a two-dimensional representation of determinant `1` when
`|G|` is invertible in `k`. -/
theorem isSymm_mckayMatrix_of_finrank_eq_two_of_det_eq_one [Group G] [Invertible (Nat.card G : k)]
    {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    (mckayMatrix V).IsSymm :=
  isSymm_mckayMatrix_of_equiv_dual
    (_root_.Representation.nonempty_equiv_dual_of_finrank_eq_two_of_det_eq_one V.ρ hdim hdet)

/-- **Diagonal vanishing of the McKay matrix** for a faithful two-dimensional representation of
determinant `1` of a nontrivial finite group over an algebraically closed field of characteristic
zero. -/
theorem mckayMatrix_apply_self_eq_zero [IsAlgClosed k] [CharZero k] [Group G] [Finite G]
    [Nontrivial G] {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hfaithful : Function.Injective V.ρ) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1)
    (c : SimpleClasses (FDRep k G)) :
    mckayMatrix V c c = 0 := by
  induction c using SimpleClasses.ind with
  | h X =>
    rw [mckayMatrix_classOf_classOf]
    exact FDRep.finrank_hom_tensor_self_eq_zero V hdim hfaithful hdet X

section Semisimple

variable [IsAlgClosed k] [Group G] [Invertible (Nat.card G : k)]

/-- For a finite group `G` over an algebraically closed field `k` in which the group order `|G|`
is invertible, the column sum of `mckayMatrix V` against the irreducible dimensions is
`∑ c₁, mckayMatrix V c₁ c₂ * c₁.finrank = dim V * c₂.finrank`. -/
theorem sum_mckayMatrix_mul_finrank_left [Fintype (SimpleClasses (FDRep k G))] (V : FDRep k G)
    (c₂ : SimpleClasses (FDRep k G)) :
    ∑ c₁ : SimpleClasses (FDRep k G), mckayMatrix V c₁ c₂ * c₁.finrank =
      Module.finrank k V * c₂.finrank := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  induction c₂ using SimpleClasses.ind with
  | h Y =>
    simp_rw [mckayMatrix_apply_classOf, SimpleClasses.finrank_classOf]
    rw [← FDRep.finrank_eq_sum_finrankHom_mul_finrank (V ⊗ Y), FDRep.finrank_tensor]

/-- Left multiplication of `mckayMatrix V` by the vector of simple dimensions scales it by
`Module.finrank k V`. -/
theorem finrank_vecMul_mckayMatrix [Fintype (SimpleClasses (FDRep k G))] (V : FDRep k G) :
    SimpleClasses.finrank ᵥ* mckayMatrix V = Module.finrank k V • SimpleClasses.finrank := by
  ext c₂
  simpa [Matrix.vecMul, dotProduct, mul_comm, Pi.smul_apply, smul_eq_mul] using
    sum_mckayMatrix_mul_finrank_left V c₂

/-- **Dimension eigenvector equation `M δ = (dim V) δ`** (equivalently, `δ` is a null vector
of `(dim V) I - M`). For a finite group `G` over an algebraically closed field `k` in which the
group order `|G|` is invertible, every `V : FDRep k G` satisfies
`∑ c₂, mckayMatrix V c₁ c₂ * c₂.finrank = dim V * c₁.finrank`. -/
theorem sum_mckayMatrix_mul_finrank [Fintype (SimpleClasses (FDRep k G))] (V : FDRep k G)
    (c₁ : SimpleClasses (FDRep k G)) :
    ∑ c₂ : SimpleClasses (FDRep k G), mckayMatrix V c₁ c₂ * c₂.finrank =
      Module.finrank k V * c₁.finrank := by
  have hentry (c₂ : SimpleClasses (FDRep k G)) :
      mckayMatrix V c₁ c₂ = mckayMatrix (ᘁV : FDRep k G) c₂ c₁ := by
    rw [← mckayMatrix_transpose, Matrix.transpose_apply]
  simp_rw [hentry]
  rw [sum_mckayMatrix_mul_finrank_left (ᘁV : FDRep k G) c₁, FDRep.finrank_leftDual]

/-- **Dimension eigenvector equation `M *ᵥ δ = (dim V) • δ`** on the vector
`SimpleClasses.finrank`. -/
theorem mckayMatrix_mulVec_finrank [Fintype (SimpleClasses (FDRep k G))] (V : FDRep k G) :
    mckayMatrix V *ᵥ SimpleClasses.finrank = Module.finrank k V • SimpleClasses.finrank := by
  ext c₁
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
    sum_mckayMatrix_mul_finrank V c₁

/-- **Multiplicativity on tensor products for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_tensor [Fintype (SimpleClasses (FDRep k G))] (V W : FDRep k G) :
    mckayMatrix (V ⊗ W) = mckayMatrix V * mckayMatrix W := by
  classical
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  refine Matrix.map_injective (Nat.cast_injective (R := ℤ)) ?_
  dsimp only
  rw [← Nat.coe_castRingHom, Matrix.map_mul, Nat.coe_castRingHom,
    mckayMatrix_map_natCast_eq_leftMulMatrix, mckayMatrix_map_natCast_eq_leftMulMatrix,
    mckayMatrix_map_natCast_eq_leftMulMatrix, ← map_mul, SplitK0.of_mul_of]

/-- **The McKay matrix of a tensor power is the corresponding power of the McKay matrix.** -/
@[simp]
theorem mckayMatrix_tensorPower [Fintype (SimpleClasses (FDRep k G))]
    [DecidableEq (SimpleClasses (FDRep k G))] (V : FDRep k G) (n : ℕ) :
    mckayMatrix (V.tensorPower n) = mckayMatrix V ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, mckayMatrix_congr V.tensorPowerZeroIsoTensorUnit, mckayMatrix_tensorUnit]
  | succ n ih =>
    rw [pow_succ', mckayMatrix_congr (V.tensorPowerSuccIso n), mckayMatrix_tensor, ih]

/-- **Under split semisimplicity, powers of the McKay matrix count tensor-power
multiplicities.** -/
@[simp]
theorem mckayMatrix_pow_apply_classOf [Fintype (SimpleClasses (FDRep k G))]
    [DecidableEq (SimpleClasses (FDRep k G))] (V : FDRep k G) (n : ℕ)
    (c₁ : SimpleClasses (FDRep k G)) (Y : FDRep k G) [Simple Y] :
    (mckayMatrix V ^ n) c₁ (SimpleClasses.classOf Y) =
      c₁.finrankHom (V.tensorPower n ⊗ Y) := by
  rw [← mckayMatrix_tensorPower, mckayMatrix_apply_classOf]

/-- **Under split semisimplicity, entries at the trivial column of `mckayMatrix V ^ n` count
multiplicities in `V^⊗n`.** -/
@[simp]
theorem mckayMatrix_pow_apply_trivial [Fintype (SimpleClasses (FDRep k G))]
    [DecidableEq (SimpleClasses (FDRep k G))] (V : FDRep k G) (n : ℕ)
    (c : SimpleClasses (FDRep k G)) :
    (mckayMatrix V ^ n) c (SimpleClasses.trivial k G) = c.finrankHom (V.tensorPower n) := by
  rw [← mckayMatrix_tensorPower, mckayMatrix_apply_trivial]

end Semisimple

/-- **Reachability to the trivial class in the McKay graph.** For a finite group `G` and a
faithful representation `V : FDRep ℂ G`, every simple isomorphism class reaches
`SimpleClasses.trivial ℂ G` along distinct positive entries of `mckayMatrix V`. -/
theorem reflTransGen_mckayMatrix_trivial {G : Type u} [Group G] [Finite G] (V : FDRep ℂ G)
    (hfaithful : Function.Injective V.ρ) (c : SimpleClasses (FDRep ℂ G)) :
    Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < mckayMatrix V x y)
      c (SimpleClasses.trivial ℂ G) := by
  classical
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ := Fintype.ofFinite (SimpleClasses (FDRep ℂ G))
  obtain ⟨n, -, hn⟩ : ∃ n < V.characterValueCount, 0 < c.finrankHom (V.tensorPower n) := by
    induction c using SimpleClasses.ind with
    | h X =>
      simp_rw [SimpleClasses.finrankHom_classOf]
      exact FDRep.exists_pos_finrank_hom_tensorPower V X hfaithful
        (FDRep.isIrreducible_of_simple X).finrank_pos
  rw [← mckayMatrix_pow_apply_trivial V n c] at hn
  exact Matrix.reflTransGen_ne_and_pos_of_pow_pos (mckayMatrix V) hn

end McKayMatrix

end FDRep

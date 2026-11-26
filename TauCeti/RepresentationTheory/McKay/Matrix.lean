/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.CategoryTheory.Action.EssentiallySmall
public import TauCeti.CategoryTheory.Semisimple.GrothendieckRing
public import TauCeti.RepresentationTheory.CharacterTable.Multiplicity
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.FDRep.Rigid
public import TauCeti.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.Tensor.Power
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.LinearAlgebra.Determinant.FiniteOrder
import TauCeti.LinearAlgebra.Matrix.Connected
import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
import TauCeti.RepresentationTheory.InvariantForm.Determinant
import TauCeti.RepresentationTheory.Irreducible

/-!
# The McKay matrix and tensor-power multiplicities

For an object `V` of `FDRep k G`, the **McKay matrix** `FDRep.mckayMatrix V` (`V.mckayMatrix`) is
the matrix indexed by `TauCeti.SimpleFDRepClasses k G` whose `(c₁, c₂)` entry is
`dim_k Hom_G(X, V ⊗ Y)` for representatives `c₁ = [X]` and `c₂ = [Y]`; under split semisimplicity
(for instance over an algebraically closed field in which `|G|` is invertible), this is the
multiplicity of `c₁` in `V ⊗ Y`. This file establishes its loop-freeness for a nontrivial finite
group `G` on faithful two-dimensional representations of determinant `1` over an algebraically
closed field of characteristic zero, its duality `(V.mckayMatrix)ᵀ = (ᘁV).mckayMatrix` and
symmetry under self-duality, its comparison with `TauCeti.fusionMatrix` and with left
multiplication on `TauCeti.SplitK0 (FDRep k G)`, the column-sum identity and dimension null-vector
equation `M δ = (dim V) δ` (for finite groups over an algebraically closed field in which the group
order `|G|` is invertible), the identification `(V.tensorPower n).mckayMatrix = V.mckayMatrix ^ n`
with its entry formulas, and reachability to the trivial class for faithful complex representations.

## Main definitions and results

* `FDRep.mckayMatrix`: the matrix `(c₁, c₂) ↦ dim_k Hom_G(X, V ⊗ Y)` on `SimpleFDRepClasses k G`,
  with `FDRep.mckayMatrix_apply_trivial`, `FDRep.mckayMatrix_zero`, `FDRep.mckayMatrix_biprod`,
  `FDRep.mckayMatrix_tensorUnit`, `FDRep.mckayMatrix_tensor`, and `FDRep.mckayMatrix_res_apply`.
* `FDRep.finrank_hom_tensor_self_eq_zero_of_central`, `FDRep.finrank_hom_tensor_self_eq_zero`, and
  `FDRep.mckayMatrix_apply_self_eq_zero`: loop-freeness for faithful two-dimensional
  representations of determinant `1` of a nontrivial finite group.
* `FDRep.mckayMatrix_transpose`, `FDRep.isSymm_mckayMatrix_of_equiv_dual`, and
  `FDRep.isSymm_mckayMatrix_of_finrank_eq_two`: transpose via `ᘁV` and symmetry.
* `FDRep.reindex_mckayMatrix_eq_transpose_fusionMatrix`: reindexing `V.mckayMatrix` along
  `SimpleFDRepClasses.equivSimpleClasses` recovers `(fusionMatrix k (SimpleClasses.classOf V))ᵀ`
  for simple `V`.
* `FDRep.reindex_mckayMatrix_eq_leftMulMatrix`: reindexing the integer-cast `V.mckayMatrix` along
  `SimpleFDRepClasses.equivSimpleClasses` recovers `Algebra.leftMulMatrix` by `SplitK0.of V` in
  `SplitK0.simpleBasis (FDRep k G)` for any `V`.
* `FDRep.sum_mckayMatrix_mul_finrank_left` and `FDRep.sum_mckayMatrix_mul_finrank`:
  column-sum identity and null-vector equation `M δ = (dim V) δ` for finite groups over an
  algebraically closed field in which the group order `|G|` is invertible.
* `FDRep.mckayMatrix_tensorPower`, `FDRep.mckayMatrix_pow_apply`, and
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
open scoped MonoidAlgebra TensorProduct

universe u v w

namespace FDRep

section LoopFree

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Over an algebraically closed field, if a central group element `g₀` has no eigenvalue `1` on
`V`, then `dim_k Hom_G(X, V ⊗ X) = 0` for every simple object `X : FDRep k G`. -/
theorem finrank_hom_tensor_self_eq_zero_of_central [IsAlgClosed k] {V : FDRep k G}
    {g₀ : G} (hcomm : ∀ h : G, g₀ * h = h * g₀) (hev : ¬ Module.End.HasEigenvalue (V.ρ g₀) 1)
    (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  have hX : _root_.Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  obtain ⟨μ, hμ⟩ := hX.exists_forall_apply_eq_smul (X.ρ g₀) fun h x ↦ by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hcomm h]
  have hμ0 : μ ≠ 0 := by
    have : Nontrivial X := hX.nontrivial
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
    rintro rfl; apply hx₀
    calc x₀ = X.ρ (g₀⁻¹ * g₀) x₀ := by simp
      _ = X.ρ g₀⁻¹ (X.ρ g₀ x₀) := by rw [map_mul, mul_apply_eq_comp]
      _ = 0 := by rw [hμ x₀, zero_smul, map_zero]
  suffices Subsingleton (X ⟶ V ⊗ X) from Module.finrank_zero_of_subsingleton
  refine ⟨fun φ ψ ↦ sub_eq_zero.mp ?_⟩
  set f : X ⟶ V ⊗ X := φ - ψ
  apply Action.hom_ext; apply FGModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  set z : V ⊗[k] X := f.hom.hom.hom x
  have heq : (V ⊗ X : FDRep k G).ρ g₀ z = μ • z := by
    simpa only [LinearMap.comp_apply, hμ x, map_smul] using
      (LinearMap.congr_fun (FDRep.hom_hom_hom_comm f g₀) x).symm
  have htens : (V ⊗ X : FDRep k G).ρ g₀ = μ • (V.ρ g₀).rTensor X := by
    have hX_map : X.ρ g₀ = μ • LinearMap.id := by
      ext y
      simp [hμ y]
    rw [FDRep.tensor_ρ, hX_map]
    exact TensorProduct.ext' fun v y ↦ by simp [TensorProduct.tmul_smul]
  rw [htens, LinearMap.smul_apply] at heq
  have hz : (V.ρ g₀).rTensor X z = z := smul_right_injective _ hμ0 heq
  have hker : LinearMap.ker (V.ρ g₀ - 1) = ⊥ := by
    simpa [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def] using hev
  obtain ⟨L, hL⟩ := (V.ρ g₀ - 1).exists_leftInverse_of_injective hker
  have hz0 : ((V.ρ g₀ - 1).rTensor X) z = 0 := by simp [hz, Module.End.one_eq_id]
  simp only [Action.zero_hom, ← CategoryTheory.ObjectProperty.ι_map, Functor.map_zero,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  calc
    z = (LinearMap.id.rTensor X) z := by simp
    _ = ((L ∘ₗ (V.ρ g₀ - 1)).rTensor X) z := by rw [hL]
    _ = (L.rTensor X) (((V.ρ g₀ - 1).rTensor X) z) := by
      rw [LinearMap.rTensor_comp, LinearMap.comp_apply]
    _ = 0 := by rw [hz0, map_zero]

/-- A reducible faithful semisimple two-dimensional representation of determinant `1` has a
central group element without eigenvalue `1`. -/
private theorem exists_central_no_eigenvalue_one_of_not_isIrreducible [Nontrivial G]
    {W₀ : Type*} [AddCommGroup W₀] [Module k W₀]
    {ρ : _root_.Representation k G W₀} [ρ.IsSemisimpleRepresentation]
    (hdim : Module.finrank k W₀ = 2)
    (hfaithful : Function.Injective ρ) (hdet : ∀ g : G, LinearMap.det (ρ g) = 1)
    (hρ : ¬ ρ.IsIrreducible) :
    ∃ g₀ : G, (∀ h : G, g₀ * h = h * g₀) ∧ ¬ Module.End.HasEigenvalue (ρ g₀) 1 := by
  -- Split `ρ` into two complementary invariant lines on which `G` acts by scalars.
  obtain ⟨W, W', hWW', hW1, hW'1⟩ :=
    _root_.Representation.exists_isCompl_finrank_eq_one_of_not_isIrreducible hdim hρ
  let e := _root_.Subrepresentation.equivProdOfIsCompl hWW'
  have : FiniteDimensional k W.toSubmodule := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional k W'.toSubmodule := Module.finite_of_finrank_pos (by omega)
  have he_apply (g : G) (v : W₀) :
      e (ρ g v) =
        (LinearMap.det (W.toRepresentation g) • (e v).1,
          LinearMap.det (W'.toRepresentation g) • (e v).2) := by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    exact Prod.ext
      (by simpa [LinearMap.apply_eq_det_smul_of_finrank_eq_one hW1] using congrArg Prod.fst h)
      (by simpa [LinearMap.apply_eq_det_smul_of_finrank_eq_one hW'1] using congrArg Prod.snd h)
  have hdet_prod (g : G) :
      LinearMap.det (W.toRepresentation g) * LinearMap.det (W'.toRepresentation g) = 1 :=
    (e.det_apply_eq_mul_of_prod g).symm.trans (hdet g)
  have hcomm (g h : G) : g * h = h * g :=
    hfaithful <| LinearMap.ext fun v ↦ e.injective <| by
      simp [map_mul, mul_apply_eq_comp, he_apply, smul_smul, mul_comm]
  -- Any `g₀ ≠ 1` is central with diagonal eigenvalues `det (W g₀), det (W' g₀) ≠ 1`.
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
  have hne_one :
      ¬ (LinearMap.det (W.toRepresentation g₀) = 1 ∧
          LinearMap.det (W'.toRepresentation g₀) = 1) := fun ⟨h1, h2⟩ ↦
    hg₀ <| hfaithful <| by
      rw [map_one]; exact LinearMap.ext fun v ↦ e.injective (by simp [he_apply, h1, h2])
  have hc₁_ne : LinearMap.det (W.toRepresentation g₀) ≠ 1 := fun h1 ↦
    hne_one ⟨h1, by simpa [h1] using hdet_prod g₀⟩
  have hc₂_ne : LinearMap.det (W'.toRepresentation g₀) ≠ 1 := fun h2 ↦
    hne_one ⟨by simpa [h2] using hdet_prod g₀, h2⟩
  exact ⟨g₀, hcomm g₀, e.not_hasEigenvalue_of_prod_finrank_eq_one hW1 hW'1 hc₁_ne hc₂_ne⟩

/-- **Loop-freeness of the McKay graph.** For a nontrivial finite group `G` and a faithful
two-dimensional representation `V : FDRep k G` of determinant `1` over an algebraically closed
field `k` of characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. -/
theorem finrank_hom_tensor_self_eq_zero [IsAlgClosed k] [CharZero k] [Finite G] [Nontrivial G]
    (V : FDRep k G) (hdim : Module.finrank k V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  by_cases hV : Simple V
  · have : _root_.Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
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
    have hev : ¬ Module.End.HasEigenvalue (V.ρ g₀) 1 := by
      intro hev
      obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
      have hv_fix : V.ρ g₀ v = v := by simpa using Module.End.mem_eigenspace_iff.mp hv
      rw [hVg₀, LinearMap.neg_apply, Module.End.one_eq_id, LinearMap.id_apply,
        neg_eq_iff_add_eq_zero, ← two_smul k v] at hv_fix
      exact hv0 ((smul_eq_zero.mp hv_fix).resolve_left two_ne_zero)
    exact finrank_hom_tensor_self_eq_zero_of_central hcomm hev X
  · have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨g₀, hcomm, hev⟩ :=
      exists_central_no_eigenvalue_one_of_not_isIrreducible
        hdim hfaithful hdet (mt (FDRep.simple_iff_isIrreducible V).mpr hV)
    exact finrank_hom_tensor_self_eq_zero_of_central hcomm hev X

end LoopFree

section McKayMatrix

open TauCeti

variable {k : Type u} {G : Type v} [Field k]

/-- **The McKay matrix** of `V : FDRep k G`, indexed by `SimpleFDRepClasses k G`, with `(c₁, c₂)`
entry `dim_k Hom_G(X, V ⊗ Y)` for representatives `c₁ = [X]` and `c₂ = [Y]` (the multiplicity of
`c₁` in `V ⊗ Y` under split semisimplicity). -/
noncomputable def mckayMatrix [Monoid G] (V : FDRep k G) :
    Matrix (SimpleFDRepClasses k G) (SimpleFDRepClasses k G) ℕ :=
  fun c₁ c₂ ↦ c₂.lift (fun Y ↦ c₁.finrankHom (V ⊗ Y)) fun _ _ _ _ ⟨iso⟩ ↦
    c₁.finrankHom_congr (whiskerLeftIso V iso)

@[simp]
theorem mckayMatrix_apply_mk [Monoid G] (V : FDRep k G) (c₁ : SimpleFDRepClasses k G)
    (Y : FDRep k G) [Simple Y] :
    mckayMatrix V c₁ (SimpleFDRepClasses.mk Y) = c₁.finrankHom (V ⊗ Y) :=
  SimpleFDRepClasses.lift_mk Y

/-- Entry `(mk X, mk Y)` of `mckayMatrix V` is `dim_k Hom_G(X, V ⊗ Y)`. -/
theorem mckayMatrix_mk_mk [Monoid G] (V X Y : FDRep k G) [Simple X] [Simple Y] :
    mckayMatrix V (SimpleFDRepClasses.mk X) (SimpleFDRepClasses.mk Y) =
      Module.finrank k (X ⟶ V ⊗ Y) := by
  rw [mckayMatrix_apply_mk, SimpleFDRepClasses.finrankHom_mk]

/-- Entry `(c, trivial)` of `mckayMatrix V` is `c.finrankHom V` (the multiplicity of `c` in `V`
under split semisimplicity). -/
@[simp]
theorem mckayMatrix_apply_trivial [Monoid G] (V : FDRep k G) (c : SimpleFDRepClasses k G) :
    mckayMatrix V c (SimpleFDRepClasses.trivial k G) = c.finrankHom V := by
  rw [← SimpleFDRepClasses.mk_tensorUnit, mckayMatrix_apply_mk]
  exact c.finrankHom_congr (ρ_ V)

/-- Isomorphic objects in `FDRep k G` have the same McKay matrix. -/
theorem mckayMatrix_congr [Monoid G] {V₁ V₂ : FDRep k G} (iso : V₁ ≅ V₂) :
    mckayMatrix V₁ = mckayMatrix V₂ := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, mckayMatrix_apply_mk]
    exact c₁.finrankHom_congr (whiskerRightIso iso Y)

/-- **Naturality of the McKay matrix under a monoid isomorphism.** Restricting `V : FDRep k G₂`
along `φ : G₁ ≃* G₂` pulls back `mckayMatrix V` along `SimpleFDRepClasses.resEquiv k φ`. -/
@[simp]
theorem mckayMatrix_res_apply {k : Type u} {G₁ : Type v} {G₂ : Type w} [Field k]
    [Monoid G₁] [Monoid G₂] (φ : G₁ ≃* G₂) (V : FDRep k G₂)
    (c₁ c₂ : SimpleFDRepClasses k G₂) :
    mckayMatrix ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj V)
        (SimpleFDRepClasses.resEquiv k φ c₁) (SimpleFDRepClasses.resEquiv k φ c₂) =
      mckayMatrix V c₁ c₂ := by
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [SimpleFDRepClasses.resEquiv_mk, mckayMatrix_apply_mk, mckayMatrix_apply_mk,
      (SimpleFDRepClasses.resEquiv k φ c₁).finrankHom_congr (FDRep.resTensorIso (φ : G₁ →* G₂) V Y),
      SimpleFDRepClasses.finrankHom_resEquiv]

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
    rw [c₁.finrankHom_congr hzero.isoZero, SimpleFDRepClasses.finrankHom_zero]

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
    exact (c₁.finrankHom_congr
      ((CategoryTheory.MonoidalCategory.tensorRight Y).mapBiprod V₁ V₂)).trans
      (c₁.finrankHom_biprod (V₁ ⊗ Y) (V₂ ⊗ Y))

/-- **Identity law for the McKay matrix** over an algebraically closed field. -/
@[simp]
theorem mckayMatrix_tensorUnit [IsAlgClosed k] [Monoid G] [DecidableEq (SimpleFDRepClasses k G)] :
    mckayMatrix (𝟙_ (FDRep k G)) = 1 := by
  ext c₁ c₂
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_apply_mk, c₁.finrankHom_congr (λ_ Y), c₁.finrankHom_simple Y,
      Matrix.one_apply]

/-- **Transpose of the McKay matrix.** When `|G|` is invertible in `k`, `(mckayMatrix V)ᵀ` is the
McKay matrix of the categorical left dual `ᘁV`. -/
@[simp]
theorem mckayMatrix_transpose [Group G] [Invertible (Nat.card G : k)] (V : FDRep k G) :
    (mckayMatrix V).transpose = mckayMatrix (ᘁV : FDRep k G) := by
  ext c₁ c₂
  induction c₁ using SimpleFDRepClasses.ind with | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with | h Y hY =>
    rw [Matrix.transpose_apply, mckayMatrix_mk_mk, mckayMatrix_mk_mk]
    exact FDRep.finrank_hom_tensor_leftDual V Y X

/-- **Bridge between the McKay matrix and the fusion matrix.** When `|G|` is invertible in `k`,
for any simple object `V : FDRep k G`, reindexing `mckayMatrix V` along
`SimpleFDRepClasses.equivSimpleClasses` gives the transpose of `TauCeti.fusionMatrix`. -/
theorem reindex_mckayMatrix_eq_transpose_fusionMatrix [Group G] [Invertible (Nat.card G : k)]
    (V : FDRep k G) [Simple V] :
    Matrix.reindex (SimpleFDRepClasses.equivSimpleClasses k G)
        (SimpleFDRepClasses.equivSimpleClasses k G) (mckayMatrix V) =
      (fusionMatrix k (SimpleClasses.classOf V)).transpose := by
  ext S T
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    fusionMatrix_apply, fusionCoeff_def, SimpleFDRepClasses.equivSimpleClasses_symm_apply,
    mckayMatrix_mk_mk]
  rw [FDRep.finrank_hom_comm]
  exact (Linear.homCongr k (whiskerRightIso (SimpleClasses.classOfReprIso V).symm T.repr)
    (Iso.refl S.repr)).finrank_eq

/-- **Bridge between the McKay matrix and the representation ring.** Over an algebraically closed
field `k` in which `|G|` is nonzero, for any `V : FDRep k G` (not necessarily simple), reindexing
the integer-cast McKay matrix along `SimpleFDRepClasses.equivSimpleClasses` gives the matrix of
left multiplication by `SplitK0.of V` in `SplitK0.simpleBasis (FDRep k G)`. -/
theorem reindex_mckayMatrix_eq_leftMulMatrix [IsAlgClosed k] [Group G] [NeZero (Nat.card G : k)]
    [Fintype (SimpleClasses (FDRep k G))] [DecidableEq (SimpleClasses (FDRep k G))]
    (V : FDRep k G) :
    Matrix.reindex (SimpleFDRepClasses.equivSimpleClasses k G)
        (SimpleFDRepClasses.equivSimpleClasses k G)
        ((mckayMatrix V).map (Nat.cast : ℕ → ℤ)) =
      Algebra.leftMulMatrix (SplitK0.simpleBasis (FDRep k G)) (SplitK0.of V) := by
  ext S T
  simp [Algebra.leftMulMatrix_eq_repr_mul, SimpleFDRepClasses.equivSimpleClasses_symm_apply,
    finrank_hom_simple_eq_simpleMultiplicities (k := k), SimpleClasses.classOf_repr]

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

/-- For a finite group `G` over an algebraically closed field `k` in which the group order `|G|`
is invertible, the column sum of `mckayMatrix V` against the irreducible dimensions is
`∑ c₁, mckayMatrix V c₁ c₂ * c₁.finrank = dim V * c₂.finrank`. -/
theorem sum_mckayMatrix_mul_finrank_left [Fintype (SimpleFDRepClasses k G)] (V : FDRep k G)
    (c₂ : SimpleFDRepClasses k G) :
    ∑ c₁ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₁.finrank =
      Module.finrank k V * c₂.finrank := by
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    simp_rw [mckayMatrix_apply_mk, SimpleFDRepClasses.finrank_mk]
    rw [← FDRep.finrank_eq_sum_finrankHom_mul_finrank (V ⊗ Y), FDRep.finrank_tensor]

/-- **Null-vector equation `M δ = (dim V) δ`.** For a finite group `G` over an algebraically closed
field `k` in which the group order `|G|` is invertible, every `V : FDRep k G` satisfies
`∑ c₂, mckayMatrix V c₁ c₂ * c₂.finrank = dim V * c₁.finrank`. -/
theorem sum_mckayMatrix_mul_finrank [Fintype (SimpleFDRepClasses k G)] (V : FDRep k G)
    (c₁ : SimpleFDRepClasses k G) :
    ∑ c₂ : SimpleFDRepClasses k G, mckayMatrix V c₁ c₂ * c₂.finrank =
      Module.finrank k V * c₁.finrank := by
  have hentry (c₂ : SimpleFDRepClasses k G) :
      mckayMatrix V c₁ c₂ = mckayMatrix (ᘁV : FDRep k G) c₂ c₁ := by
    rw [← mckayMatrix_transpose, Matrix.transpose_apply]
  simp_rw [hentry]
  rw [sum_mckayMatrix_mul_finrank_left (ᘁV : FDRep k G) c₁, FDRep.finrank_leftDual]

/-- **Multiplicativity on tensor products for the McKay matrix.** -/
@[simp]
theorem mckayMatrix_tensor [Fintype (SimpleFDRepClasses k G)] (V W : FDRep k G) :
    mckayMatrix (V ⊗ W) = mckayMatrix V * mckayMatrix W := by
  classical
  let _ : Fintype (SimpleClasses (FDRep k G)) :=
    Fintype.ofEquiv _ (SimpleFDRepClasses.equivSimpleClasses k G)
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  let e := SimpleFDRepClasses.equivSimpleClasses k G
  have hre :
      Matrix.reindex e e ((mckayMatrix (V ⊗ W)).map (Nat.cast : ℕ → ℤ)) =
        Matrix.reindex e e ((mckayMatrix V * mckayMatrix W).map (Nat.cast : ℕ → ℤ)) := by
    rw [reindex_mckayMatrix_eq_leftMulMatrix (V ⊗ W), ← SplitK0.of_mul_of, map_mul,
      ← reindex_mckayMatrix_eq_leftMulMatrix V, ← reindex_mckayMatrix_eq_leftMulMatrix W]
    simp only [e, ← Nat.coe_castRingHom, Matrix.map_mul, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv]
  ext c₁ c₂
  have h := congr_fun (congr_fun hre (e c₁)) (e c₂)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm_apply_apply,
    Matrix.map_apply] at h
  exact Nat.cast_injective h

/-- **The McKay matrix of a tensor power is the corresponding power of the McKay matrix.** -/
@[simp]
theorem mckayMatrix_tensorPower [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ) :
    mckayMatrix (V.tensorPower n) = mckayMatrix V ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, mckayMatrix_congr V.tensorPowerZeroIsoTensorUnit, mckayMatrix_tensorUnit]
  | succ n ih =>
    rw [pow_succ', mckayMatrix_congr (V.tensorPowerSuccIso n), mckayMatrix_tensor, ih]

/-- **Under split semisimplicity, powers of the McKay matrix count tensor-power
multiplicities.** -/
@[simp]
theorem mckayMatrix_pow_apply [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ)
    (c₁ : SimpleFDRepClasses k G) (Y : FDRep k G) [Simple Y] :
    (mckayMatrix V ^ n) c₁ (SimpleFDRepClasses.mk Y) =
      c₁.finrankHom (V.tensorPower n ⊗ Y) := by
  rw [← mckayMatrix_tensorPower, mckayMatrix_apply_mk]

/-- **Under split semisimplicity, entries at the trivial column of `mckayMatrix V ^ n` count
multiplicities in `V^⊗n`.** -/
@[simp]
theorem mckayMatrix_pow_apply_trivial [Fintype (SimpleFDRepClasses k G)]
    [DecidableEq (SimpleFDRepClasses k G)] (V : FDRep k G) (n : ℕ)
    (c : SimpleFDRepClasses k G) :
    (mckayMatrix V ^ n) c (SimpleFDRepClasses.trivial k G) = c.finrankHom (V.tensorPower n) := by
  rw [← mckayMatrix_tensorPower, mckayMatrix_apply_trivial]

end Semisimple

/-- **Reachability to the trivial class in the McKay graph.** For a finite group `G` and a
faithful representation `V : FDRep ℂ G`, every simple isomorphism class reaches
`SimpleFDRepClasses.trivial ℂ G` along distinct positive entries of `mckayMatrix V`. -/
theorem reflTransGen_mckayMatrix_trivial {G : Type u} [Group G] [Finite G] (V : FDRep ℂ G)
    (hfaithful : Function.Injective V.ρ) (c : SimpleFDRepClasses ℂ G) :
    Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < mckayMatrix V x y)
      c (SimpleFDRepClasses.trivial ℂ G) := by
  classical
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ := Fintype.ofFinite (SimpleFDRepClasses ℂ G)
  obtain ⟨n, -, hn⟩ : ∃ n < V.characterValueCount, 0 < c.finrankHom (V.tensorPower n) := by
    induction c using SimpleFDRepClasses.ind with
    | h X hX =>
      simp_rw [SimpleFDRepClasses.finrankHom_mk]
      exact FDRep.exists_pos_finrank_hom_tensorPower V X hfaithful
        (FDRep.isIrreducible_of_simple X).finrank_pos
  rw [← mckayMatrix_pow_apply_trivial V n c] at hn
  exact Matrix.reflTransGen_ne_and_pos_of_pow_pos (mckayMatrix V) hn

end McKayMatrix

end FDRep

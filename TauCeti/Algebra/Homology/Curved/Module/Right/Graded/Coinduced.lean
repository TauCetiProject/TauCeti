/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Induced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective

/-!
# Coinduced curved right modules from graded right modules

Dual to induction, every graded right module $N$ over a curved differential graded algebra
$(A, d, w)$ gives rise to a coinduced curved right module $G^- N$. Up to swapping the two summands
of $N \oplus N$, $G^- N$ coincides with the induced curved module $G^+(N\{-1\})$ on the grading
shift of $N$: over the ground ring its underlying module is $N \oplus N$, graded with degree-$p$
piece $N_p \oplus N_{p + 1}$, its right $A$-action is twisted on the second factor by the algebra
differential and a Koszul sign
$$(x, y) \cdot a = (x \cdot a,\ y \cdot a + (-1)^{|x|} x \cdot d a),$$
and its curved differential is $D_-(x, y) = (y, x \cdot w)$.

Coinduction furnishes the right adjoint to forgetting the differential from curved right modules
with closed degree-zero morphisms to graded right modules: a graded morphism $M \longrightarrow N$
lifts to the closed morphism $M \longrightarrow G^- N$ given by $m \mapsto (f(m), f(d_M m))$.
Every coinduced curved module is contractible in the curved homotopy category, and after forgetting
the differential $G^- N$ sits in a natural short exact sequence
$0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$
of graded right modules. Thus $G^- I$ is graded-injective whenever $I$ is injective, and every
curved right module embeds via a closed monomorphism into such a contractible graded-injective
curved module.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj`: the coinduced curved right module $G^- N$
  associated to a graded right module $N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedEquiv`: the ground-ring linear equivalence identifying
  the carrier of $G^- N$ with $N \times N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedInr`, `TauCeti.CurvedDGRightModuleCat.coinducedFst`:
  the graded inclusion $N\{-1\} \longrightarrow G^- N$ and projection $G^- N \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.coinduced`: the right-adjoint functor from graded right modules
  to curved right modules with closed morphisms.
* `TauCeti.CurvedDGRightModuleCat.coinducedLift`: the closed morphism $M \longrightarrow G^- N$
  adjunct to a graded morphism $U(M) \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.forgetDifferentialCoinducedAdj`: the adjunction between
  forgetting the differential and coinduction.

## Main results

* `TauCeti.CurvedDGRightModuleCat.coinducedShortComplex_shortExact`: the graded short exact
  sequence $0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: every coinduced curved right
  module is zero in the curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.exists_mono_to_coinducedObj_injective`: every curved right module
  admits a closed monomorphism into $G^- I$ for an injective graded right module $I$.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Lemma 7.7.
-/

public section

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uN u

section CoinducedObj

open CategoryTheory MulOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- The **coinduced curved right module** `G⁻ N` associated to a graded right module `N`. Over `R`
its carrier is `N × N` with degree-`p` piece `N_p × N_{p + 1}`, twisted right action
`(x, y) · a = (x · a, y · a + (-1)^{|x|} x · d a)`, and differential `(x, y) ↦ (y, x · w)`. -/
noncomputable def coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uN} h :=
  inducedObj h (N.shiftObj (-1))

/-- The `R`-linear equivalence identifying the carrier of `coinducedObj h N` with `N × N`. -/
noncomputable def coinducedEquiv (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h N ≃ₗ[R] N × N :=
  (inducedEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N)

/-- Elements of `coinducedObj h N` are determined by their two components in `N × N`. -/
@[ext]
theorem coinducedObj_ext {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {z₁ z₂ : coinducedObj h N}
    (h₁ : (coinducedEquiv h N z₁).1 = (coinducedEquiv h N z₂).1)
    (h₂ : (coinducedEquiv h N z₁).2 = (coinducedEquiv h N z₂).2) : z₁ = z₂ :=
  (coinducedEquiv h N).injective (Prod.ext h₁ h₂)

/-- An element of `coinducedObj h N` has degree `p` if and only if its components lie in `N_p` and
`N_{p + 1}`. -/
@[simp]
theorem mem_coinducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : coinducedObj h N} :
    z ∈ (coinducedObj h N).grading p ↔
      (coinducedEquiv h N z).1 ∈ N.grading.piece p ∧
        (coinducedEquiv h N z).2 ∈ N.grading.piece (p + 1) := by
  let e := (inducedEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N)
  revert z
  change ∀ z : inducedObj h (N.shiftObj (-1)),
    z ∈ (inducedObj h (N.shiftObj (-1))).grading p ↔
      (e z).1 ∈ N.grading.piece p ∧ (e z).2 ∈ N.grading.piece (p + 1)
  intro z
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [mem_inducedObj_grading_iff, GradedModuleCat.mem_shiftObj_piece_iff,
    GradedModuleCat.mem_shiftObj_piece_iff, sub_neg_eq_add, sub_neg_eq_add, sub_add_cancel,
    and_comm]

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `coinducedObj h N`, expressed in `N × N` via
`coinducedEquiv`. -/
@[simp]
theorem coinducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : coinducedObj h N) :
    coinducedEquiv h N (a • z) =
      (a • (coinducedEquiv h N z).1,
        a • (coinducedEquiv h N z).2 + op (d a.unop) • N.grading.koszulTwist 1
          (coinducedEquiv h N z).1) := by
  let e := (inducedEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N)
  revert z
  change ∀ z : inducedObj h (N.shiftObj (-1)),
    e (a • z) = (a • (e z).1, a • (e z).2 + op (d a.unop) • N.grading.koszulTwist 1 (e z).1)
  intro z
  simp [e, InternalGrading.koszulTwist_one_shift_one, sub_neg_eq_add]

/-- The twisted right action on `coinducedObj h N`, expressed in `N × N` via `coinducedEquiv`. -/
theorem coinducedEquiv_op_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : A) (z : coinducedObj h N) :
    coinducedEquiv h N (op a • z) =
      (op a • (coinducedEquiv h N z).1,
        op a • (coinducedEquiv h N z).2 + op (d a) • N.grading.koszulTwist 1
          (coinducedEquiv h N z).1) := by
  rw [coinducedEquiv_smul, unop_op]

/-- The curved differential on `coinducedObj h N` sends `(x, y)` to `(y, x · w)`. -/
@[simp]
theorem coinducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N ((coinducedObj h N).differential z) =
      ((coinducedEquiv h N z).2, op w • (coinducedEquiv h N z).1) := by
  let e := (inducedEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N)
  revert z
  change ∀ z : inducedObj h (N.shiftObj (-1)),
    e ((inducedObj h (N.shiftObj (-1))).differential z) = ((e z).2, op w • (e z).1)
  intro z
  simp [e]

/-! ### Graded short exact sequence and injectivity -/

/-- The natural graded right-module inclusion `N{-1} ⟶ U(G⁻ N)` sending `y` to `(0, y)`. -/
noncomputable def coinducedInr (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h N) :=
  inducedInl h (N.shiftObj (-1))

/-- The graded inclusion `coinducedInr` sends `y` to `(0, y)` in `N × N`. -/
@[simp]
theorem coinducedEquiv_coinducedInr_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (y : N) :
    coinducedEquiv h N ((coinducedInr h N).hom y) = (0, y) := by
  change ((inducedEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N))
    ((inducedInl h (N.shiftObj (-1))).hom y) = (0, y)
  simp

/-- The natural graded right-module projection `U(G⁻ N) ⟶ N` sending `(x, y)` to `x`. -/
noncomputable def coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  GradedModuleCat.ofHom
    ({ toFun z := (coinducedEquiv h N z).1
       map_add' _ _ := by simp
       map_smul' _ _ := by simp } : coinducedObj h N →ₗ[Aᵐᵒᵖ] N)
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [toGradedModuleCat_piece, mem_coinducedObj_grading_iff] at hz
      simpa using hz.1)

/-- The graded projection `coinducedFst` extracts the first component in `N × N`. -/
@[simp]
theorem coinducedFst_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    (coinducedFst h N).hom z = (coinducedEquiv h N z).1 := by
  rw [coinducedFst]
  rfl

/-- The graded inclusion of `N{-1}` into `G⁻ N` followed by the graded projection onto `N`
vanishes. -/
@[reassoc (attr := simp)]
theorem coinducedInr_comp_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedInr h N ≫ coinducedFst h N = 0 := by
  ext y
  change (coinducedFst h N).hom ((coinducedInr h N).hom y) = 0
  rw [coinducedFst_apply, coinducedEquiv_coinducedInr_apply]

/-- After forgetting the differential, `G⁻ N` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ U(G⁻ N) ⟶ N ⟶ 0` of graded right modules. -/
theorem coinducedShortComplex_shortExact (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedInr h N) (coinducedFst h N)
      (coinducedInr_comp_coinducedFst h N)).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).2 fun y₁ y₂ hy ↦
    (congrArg Prod.snd (coinducedEquiv_coinducedInr_apply h N y₁)).symm.trans
      ((congrArg (fun z ↦ (coinducedEquiv h N z).2) hy).trans
        (congrArg Prod.snd (coinducedEquiv_coinducedInr_apply h N y₂)))
  epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun x ↦
    ⟨(coinducedEquiv h N).symm (x, 0), by
      change (coinducedFst h N).hom ((coinducedEquiv h N).symm (x, 0)) = x
      rw [coinducedFst_apply, LinearEquiv.apply_symm_apply]⟩
  exact := GradedModuleCat.exact_iff.2 fun z ↦ by
    change (coinducedFst h N).hom z = 0 ↔ _
    rw [coinducedFst_apply]
    refine ⟨fun hz ↦ ⟨(coinducedEquiv h N z).2, ?_⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    · exact coinducedObj_ext (by rw [coinducedEquiv_coinducedInr_apply]; exact hz.symm)
        (by rw [coinducedEquiv_coinducedInr_apply])
    · rw [← hy, coinducedEquiv_coinducedInr_apply]

/-- If `I` is an injective graded right module, the underlying graded right module of `G⁻ I` is
injective. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (coinducedObj h I)) := by
  have : Injective (I.shiftObj (-1)) := GradedModuleCat.injective_shiftObj I (-1)
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((coinducedShortComplex_shortExact h I).hasInjectiveDimensionLT_X₂ 1 inferInstance
      inferInstance)

end CoinducedObj

/-! ### Functoriality, adjunction, contractibility, and injective hulls -/

section Functor

open CategoryTheory CategoryTheory.Limits MulOpposite

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Closed morphism `G⁻ N₁ ⟶ G⁻ N₂` induced by a morphism `f : N₁ ⟶ N₂` of graded right modules. -/
noncomputable def coinducedMap (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₁) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₂) :=
  inducedMap h ((GradedModuleCat.shiftFunctor (-1)).map f)

/-- On underlying pairs in `N × N`, `coinducedMap h f` applies `f` componentwise. -/
@[simp]
theorem coinducedEquiv_coinducedMap_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    coinducedEquiv h N₂ (closedHom (coinducedMap h f) z) =
      (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2) := by
  let e₁ := (inducedEquiv h (N₁.shiftObj (-1))).trans (LinearEquiv.prodComm R N₁ N₁)
  let e₂ := (inducedEquiv h (N₂.shiftObj (-1))).trans (LinearEquiv.prodComm R N₂ N₂)
  revert z
  change ∀ z : inducedObj h (N₁.shiftObj (-1)),
    e₂ (closedHom (inducedMap h ((GradedModuleCat.shiftFunctor (-1)).map f)) z) =
      (f.hom (e₁ z).1, f.hom (e₁ z).2)
  intro z
  simp [e₁, e₂]

/-- The **coinduction functor** `N ↦ G⁻ N` from graded right modules to curved right modules with
closed degree-zero morphisms. -/
@[expose, implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)
  map f := coinducedMap h f
  map_id N := closedHom_ext fun z ↦ (coinducedEquiv h N).injective (by simp)
  map_comp f g := closedHom_ext fun z ↦ (coinducedEquiv h _).injective (by simp)

/-- The coinduction functor sends a graded right module `N` to `coinducedObj h N`. -/
@[simp]
theorem coinduced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

/-- The coinduction functor acts on morphisms by `coinducedMap`. -/
@[simp]
theorem coinduced_map (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) :
    (coinduced h).map f = coinducedMap h f :=
  (rfl)

/-- The closed morphism `M ⟶ G⁻ N` adjunct to a degree-zero right-linear map `f : M →ₗ[Aᵐᵒᵖ] N`,
sending `m` to `(f m, f (d_M m))`. -/
noncomputable def coinducedLift {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  closedHomOf
    { toFun m := (coinducedEquiv h N).symm (f m, f (M.differential m))
      map_add' _ _ := (coinducedEquiv h N).injective (by simp)
      map_smul' a m := (coinducedEquiv h N).injective <| by
        have hkey (x : M) : f (M.differential (a • x)) =
            a • f (M.differential x) + op (d a.unop) • N.grading.koszulTwist 1 (f x) := by
          induction x using DirectSum.Decomposition.inductionOn M.grading with
          | zero => simp
          | @homogeneous q x =>
            rcases x with ⟨x, hx⟩
            have hfx : f x ∈ N.grading.piece q := by simpa using hf.map_mem hx
            have ha_eq : a = op a.unop := (MulOpposite.op_unop a).symm
            conv_lhs => rw [ha_eq]
            rw [N.grading.koszulTwist_one_apply_of_mem hfx,
              M.isCurvedDGRightModule.leibniz hx a.unop, ← ha_eq, map_add, LinearMap.map_smul,
              LinearMap.map_smul_of_tower f, LinearMap.map_smul]
            simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _)]
          | add x₁ x₂ hx₁ hx₂ => simp only [smul_add, map_add, hx₁, hx₂]; abel
        simp [hkey] }
    (fun p m hm ↦ by
      rw [mem_coinducedObj_grading_iff]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
      have hdm : M.differential m ∈ M.grading (p + 1) :=
        M.isCurvedDGRightModule.isHomogeneous.map_mem hm
      exact ⟨by simpa using hf.map_mem hm, by simpa using hf.map_mem hdm⟩)
    (fun m ↦ (coinducedEquiv h N).injective <| by
      simp [M.isCurvedDGRightModule.sq_eq, f.map_smul])

/-- Evaluating the adjunct closed morphism `coinducedLift f hf` sends `m` to
`(f m, f (d_M m))`. -/
@[simp]
theorem coinducedEquiv_closedHom_coinducedLift_apply {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) (m : M) :
    coinducedEquiv h N (closedHom (coinducedLift f hf) m) = (f m, f (M.differential m)) := by
  rw [coinducedLift, closedHom_closedHomOf]
  exact (coinducedEquiv h N).apply_symm_apply _

/-- If `f : M →ₗ[Aᵐᵒᵖ] N` is an injective degree-zero right-linear map, its adjunct closed
morphism `coinducedLift f hf : M ⟶ G⁻ N` is a monomorphism in the closed category of curved right
modules. -/
theorem mono_coinducedLift_of_injective {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0)
    (hinj : Function.Injective f) :
    Mono (coinducedLift f hf) :=
  ⟨fun {K} u₁ u₂ hu ↦ closedHom_ext fun x ↦ hinj <| by
    have h₁₂ := congrArg (fun k ↦ (coinducedEquiv h N (closedHom k x)).1) hu
    simpa only [closedHom_comp, LinearMap.comp_apply,
      coinducedEquiv_closedHom_coinducedLift_apply] using h₁₂⟩

private theorem isHomogeneous_from_gradedHom {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : toGradedModuleCat M ⟶ N) :
    LinearMap.IsHomogeneous (M := M) f.hom M.grading N.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
    have hm' : m ∈ (toGradedModuleCat M).grading.piece p := by rwa [toGradedModuleCat_piece]
    exact f.isHomogeneous.map_mem hm'

/-- Forgetting the differential on curved right modules is left adjoint to coinduction
`N ↦ G⁻ N`. -/
noncomputable def forgetDifferentialCoinducedAdj (h : IsCurvedDGAlgebra 𝒜 d w) :
    forgetDifferential (h := h) ⊣ coinduced h :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun f := coinducedLift (M := ForgetEnrichment.to _ M) f.hom
            (isHomogeneous_from_gradedHom f)
          invFun g := (forgetDifferential (h := h)).map g ≫ coinducedFst h N
          left_inv f := by
            ext m
            change (coinducedFst h N).hom (closedHom (coinducedLift
              (M := ForgetEnrichment.to _ M) f.hom (isHomogeneous_from_gradedHom f)) m) = f.hom m
            rw [coinducedFst_apply, coinducedEquiv_closedHom_coinducedLift_apply]
          right_inv g := by
            let g' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
                (ForgetEnrichment.to _ M) ⟶
              ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) := g
            apply closedHom_ext
            intro m
            apply (coinducedEquiv h N).injective
            have hd := congrArg (fun z ↦ (coinducedEquiv h N z).1) (differential_closedHom g' m)
            rw [coinducedEquiv_differential] at hd
            simp only [coinducedEquiv_closedHom_coinducedLift_apply, GradedModuleCat.hom_comp,
              forgetDifferential_map_hom, LinearMap.comp_apply]
            exact Prod.ext (coinducedFst_apply h N (closedHom g' m))
              ((coinducedFst_apply h N _).trans hd.symm) }
      homEquiv_naturality_left_symm {M₁ M₂ N} k g := by
        dsimp only [Equiv.coe_fn_symm_mk]
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right {M N₁ N₂} f k := by
        apply closedHom_ext
        intro m
        apply (coinducedEquiv h N₂).injective
        dsimp only [Equiv.coe_fn_mk]
        rw [coinduced_map, closedHom_comp, LinearMap.comp_apply, coinducedEquiv_coinducedMap_apply,
          coinducedEquiv_closedHom_coinducedLift_apply,
          coinducedEquiv_closedHom_coinducedLift_apply, GradedModuleCat.hom_comp]
        rfl }

/-- Every coinduced curved right module `G⁻ N` is contractible, hence zero in the curved homotopy
category. -/
theorem isZero_homotopy_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h N)) :=
  isZero_homotopy_inducedObj h (N.shiftObj (-1))

/-- For an injective graded right module `I`, the coinduced curved module `G⁻ I` is
graded-injective. -/
theorem gradedInjective_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    gradedInjective R h (DGHomotopyCategory.of R (coinducedObj h I)) :=
  (gradedInjective_iff _).2 (inferInstanceAs (Injective (toGradedModuleCat (coinducedObj h I))))

/-- Every curved right module `M` admits a closed monomorphism into `G⁻ I` for some injective
graded right module `I`. -/
theorem exists_mono_to_coinducedObj_injective {h : IsCurvedDGAlgebra 𝒜 d w}
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
      (_ : Injective I)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h I)), Mono f := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
    rw [InternalGrading.ofDecomposition_piece]
    infer_instance
  obtain ⟨I⟩ := @EnoughInjectives.presentation _ _
    GradedModuleCat.enoughInjectives.{u, u, u} (toGradedModuleCat M)
  have : Injective I.J := I.injective
  have : Mono I.f := I.mono
  have hinj : Function.Injective (I.f.hom : M →ₗ[Aᵐᵒᵖ] I.J) :=
    (GradedModuleCat.mono_iff_injective I.f).1 inferInstance
  exact ⟨I.J, inferInstance, coinducedLift I.f.hom (isHomogeneous_from_gradedHom I.f),
    mono_coinducedLift_of_injective _ _ hinj⟩

end Functor

end TauCeti.CurvedDGRightModuleCat

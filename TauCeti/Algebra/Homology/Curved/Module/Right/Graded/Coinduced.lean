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
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Coinduced curved right modules from graded right modules

Dual to induction, every graded right module $N$ over a curved differential graded algebra
$(A, d, w)$ gives rise to a coinduced curved right module $G^- N$. Up to swapping the two summands
of $N \oplus N$, $G^- N$ coincides with $G^+(N\{-1\})$: over the ground ring its underlying module
is $N \oplus N$, graded with degree-$p$ piece $N_p \oplus N_{p + 1}$, its twisted right $A$-action
is $$(x, y) \cdot a = (x \cdot a,\ y \cdot a + (-1)^{|x|} x \cdot d a),$$ and its curved
differential is $D_-(x, y) = (y, x \cdot w)$.

Coinduction is right adjoint to forgetting the differential from curved right modules with closed
degree-zero morphisms to graded right modules, via $m \mapsto (f(m), f(d_M m))$. Every $G^- N$ is
contractible in the curved homotopy category and sits in a graded short exact sequence
$0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$. Thus $G^- I$
is graded-injective when $I$ is injective, giving closed monomorphisms into contractible
graded-injectives.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj` and `TauCeti.CurvedDGRightModuleCat.coinducedEquiv`:
  the coinduced curved right module $G^- N$ and its carrier equivalence with $N \times N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedInr`, `TauCeti.CurvedDGRightModuleCat.coinducedFst`:
  the graded inclusion $N\{-1\} \longrightarrow G^- N$ and projection $G^- N \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.coinduced`, `TauCeti.CurvedDGRightModuleCat.coinducedLift`, and
  `TauCeti.CurvedDGRightModuleCat.forgetDifferentialCoinducedAdj`: the right-adjoint functor,
  adjunct closed morphism, and adjunction with forgetting the differential.

## Main results

* `TauCeti.CurvedDGRightModuleCat.shortExact_coinducedInr_coinducedFst`: the graded short exact
  sequence $0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj` and
  `TauCeti.CurvedDGRightModuleCat.exists_mono_to_coinducedObj_injective`: contractibility of $G^- N$
  and closed monomorphisms into contractible graded-injective curved modules.

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
    {z₁ z₂ : coinducedObj h N} (h₁ : (coinducedEquiv h N z₁).1 = (coinducedEquiv h N z₂).1)
    (h₂ : (coinducedEquiv h N z₁).2 = (coinducedEquiv h N z₂).2) : z₁ = z₂ :=
  (coinducedEquiv h N).injective (Prod.ext h₁ h₂)

/-- An element of `coinducedObj h N` has degree `p` iff its components lie in `N_p` and `N_{p + 1}`.
-/
@[simp]
theorem mem_coinducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : coinducedObj h N} :
    z ∈ (coinducedObj h N).grading p ↔ (coinducedEquiv h N z).1 ∈ N.grading.piece p ∧
      (coinducedEquiv h N z).2 ∈ N.grading.piece (p + 1) := by
  unfold coinducedObj coinducedEquiv at *; simp [and_comm]

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `coinducedObj h N`, expressed in `N × N`. -/
@[simp]
theorem coinducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : coinducedObj h N) :
    coinducedEquiv h N (a • z) = (a • (coinducedEquiv h N z).1,
      a • (coinducedEquiv h N z).2 +
        op (d a.unop) • N.grading.koszulTwist 1 (coinducedEquiv h N z).1) := by
  unfold coinducedObj coinducedEquiv at *
  simp [InternalGrading.koszulTwist_one_shift_one, sub_neg_eq_add]

/-- The curved differential on `coinducedObj h N` sends `(x, y)` to `(y, x · w)`. -/
@[simp]
theorem coinducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N ((coinducedObj h N).differential z) =
      ((coinducedEquiv h N z).2, op w • (coinducedEquiv h N z).1) := by
  unfold coinducedObj coinducedEquiv at *; simp

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
    (dsimp% only (coinducedEquiv h N ((coinducedInr h N).hom y))) = (0, y) := by
  unfold coinducedObj coinducedEquiv coinducedInr; simp

/-- The natural graded right-module projection `U(G⁻ N) ⟶ N` sending `(x, y)` to `x`. -/
noncomputable def coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  GradedModuleCat.ofHom
    ({ toFun z := (coinducedEquiv h N z).1, map_add' _ _ := by simp,
       map_smul' _ _ := by simp } : coinducedObj h N →ₗ[Aᵐᵒᵖ] N)
    (LinearMap.isHomogeneous_def.2 fun _ _ hz ↦ by
      rw [toGradedModuleCat_piece, mem_coinducedObj_grading_iff] at hz; simpa using hz.1)

/-- The graded projection `coinducedFst` extracts the first component in `N × N`. -/
@[simp]
theorem coinducedFst_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) : (coinducedFst h N).hom z = (coinducedEquiv h N z).1 := by
  rw [coinducedFst]; rfl

/-- The graded inclusion of `N{-1}` into `G⁻ N` followed by `coinducedFst` vanishes. -/
@[reassoc (attr := simp)]
theorem coinducedInr_comp_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedInr h N ≫ coinducedFst h N = 0 := by ext y; simp

/-- After forgetting the differential, `G⁻ N` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ U(G⁻ N) ⟶ N ⟶ 0` of graded right modules. -/
theorem shortExact_coinducedInr_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedInr h N) (coinducedFst h N)
      (coinducedInr_comp_coinducedFst h N)).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).2 fun _ _ hy ↦ by
    simpa using congrArg (fun z : coinducedObj h N ↦ (coinducedEquiv h N z).2) hy
  epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun x ↦
    ⟨(coinducedEquiv h N).symm (x, 0), by simp⟩
  exact := GradedModuleCat.exact_iff.2 fun z ↦ by
    simp only [coinducedFst_apply, Set.mem_range]
    refine ⟨fun hz ↦ ⟨(coinducedEquiv h N z).2, ?_⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    · exact coinducedObj_ext (by rw [coinducedEquiv_coinducedInr_apply]; exact hz.symm)
        (by rw [coinducedEquiv_coinducedInr_apply])
    · rw [← hy, coinducedEquiv_coinducedInr_apply]

/-- If `I` is an injective graded right module, `U(G⁻ I)` is injective. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (coinducedObj h I)) := by
  have : Injective (I.shiftObj (-1)) := GradedModuleCat.injective_shiftObj I (-1)
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((shortExact_coinducedInr_coinducedFst h I).hasInjectiveDimensionLT_X₂ 1 inferInstance
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

/-- The **coinduction functor** `N ↦ G⁻ N` from graded right modules to curved right modules with
closed degree-zero morphisms. -/
@[expose, implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)
  map {N₁ N₂} f := closedHomOf
    { toFun z := (coinducedEquiv h N₂).symm
        (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2)
      map_add' _ _ := (coinducedEquiv h N₂).injective (by simp)
      map_smul' a z := (coinducedEquiv h N₂).injective <| by
        have htw : N₂.grading.koszulTwist 1 (f.hom (coinducedEquiv h N₁ z).1) =
            f.hom (N₁.grading.koszulTwist 1 (coinducedEquiv h N₁ z).1) := by
          simpa using (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
            f.isHomogeneous.map_mem hx : LinearMap.IsHomogeneous (f.hom.restrictScalars R)
              N₁.grading.piece N₂.grading.piece 0).koszulTwist_apply 1 _
        simp [htw] }
    (fun p z hz ↦ by
      rw [mem_coinducedObj_grading_iff] at hz ⊢
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
      exact ⟨by simpa using f.isHomogeneous.map_mem hz.1,
        by simpa using f.isHomogeneous.map_mem hz.2⟩)
    (fun z ↦ (coinducedEquiv h N₂).injective (by simp))
  map_id N := closedHom_ext fun z ↦ (coinducedEquiv h N).injective (by simp)
  map_comp f g := closedHom_ext fun z ↦ (coinducedEquiv h _).injective (by simp)

/-- The coinduction functor sends a graded right module `N` to `coinducedObj h N`. -/
@[simp]
theorem coinduced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

/-- On underlying pairs in `N × N`, `(coinduced h).map f` applies `f` componentwise. -/
@[simp]
theorem coinducedEquiv_closedHom_coinduced_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    coinducedEquiv h N₂ (closedHom ((coinduced h).map f) z) =
      (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2) := by
  dsimp only [coinduced]; rw [closedHom_closedHomOf]; exact (coinducedEquiv h N₂).apply_symm_apply _

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Additive where
  map_add := closedHom_ext fun z ↦ (coinducedEquiv h _).injective <| by rw [closedHom_add]; simp

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Linear R where
  map_smul _ _ := closedHom_ext fun z ↦ (coinducedEquiv h _).injective <| by
    rw [closedHom_smul]; simp

/-- The closed morphism `M ⟶ G⁻ N` adjunct to a morphism `f : U(M) ⟶ N` of graded right modules,
sending `m` to `(f m, f (d_M m))`. -/
noncomputable def coinducedLift {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : toGradedModuleCat M ⟶ N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  closedHomOf
    { toFun m := (coinducedEquiv h N).symm (f.hom m, f.hom (M.differential m))
      map_add' _ _ := (coinducedEquiv h N).injective (by simp)
      map_smul' a m := (coinducedEquiv h N).injective <| by
        have htw : N.grading.koszulTwist 1 (f.hom m) =
            f.hom ((InternalGrading.ofDecomposition M.grading).koszulTwist 1 m) := by
          have hf : LinearMap.IsHomogeneous (f.hom.restrictScalars R)
              (InternalGrading.ofDecomposition M.grading).piece N.grading.piece 0 :=
            LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
              f.isHomogeneous.map_mem (by simpa [toGradedModuleCat_piece] using hx)
          simpa using hf.koszulTwist_apply 1 m
        simp [M.differential_smul, htw] }
    (fun p m hm ↦ by
      rw [mem_coinducedObj_grading_iff]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
      have hm' : m ∈ (toGradedModuleCat M).grading.piece p := by rwa [toGradedModuleCat_piece]
      have hdm : M.differential m ∈ (toGradedModuleCat M).grading.piece (p + 1) := by
        rw [toGradedModuleCat_piece]; exact M.isCurvedDGRightModule.isHomogeneous.map_mem hm
      exact ⟨by simpa using f.isHomogeneous.map_mem hm',
        by simpa using f.isHomogeneous.map_mem hdm⟩)
    (fun m ↦ (coinducedEquiv h N).injective <| by
      simp [M.isCurvedDGRightModule.sq_eq, f.hom.map_smul])

/-- Evaluating the adjunct closed morphism `coinducedLift f` sends `m` to `(f m, f (d_M m))`. -/
@[simp]
theorem coinducedEquiv_closedHom_coinducedLift_apply {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : toGradedModuleCat M ⟶ N) (m : M) :
    coinducedEquiv h N (closedHom (coinducedLift f) m) = (f.hom m, f.hom (M.differential m)) := by
  rw [coinducedLift, closedHom_closedHomOf]; exact (coinducedEquiv h N).apply_symm_apply _

/-- Following `(forgetDifferential).map (coinducedLift f)` with `coinducedFst` recovers `f`. -/
@[reassoc (attr := simp)]
theorem forgetDifferential_map_coinducedLift_comp_coinducedFst {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : toGradedModuleCat M ⟶ N) :
    (forgetDifferential (h := h)).map (coinducedLift f) ≫ coinducedFst h N = f := by
  ext m
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom,
    coinducedFst_apply]
  exact congrArg Prod.fst (coinducedEquiv_closedHom_coinducedLift_apply f m)

/-- Forming `coinducedLift` from the projection of `g : M ⟶ G⁻ N` along `coinducedFst` recovers `g`.
-/
@[simp]
theorem coinducedLift_forgetDifferential_map_comp_coinducedFst {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)) :
    coinducedLift ((forgetDifferential (h := h)).map g ≫ coinducedFst h N) = g := by
  refine closedHom_ext fun m ↦ (coinducedEquiv h N).injective <| ?_
  simp only [coinducedEquiv_closedHom_coinducedLift_apply, GradedModuleCat.hom_comp,
    LinearMap.comp_apply, forgetDifferential_map_hom]
  have hd := congrArg (fun z ↦ (coinducedEquiv h N z).1) (differential_closedHom g m)
  rw [coinducedEquiv_differential] at hd; exact Prod.ext rfl hd.symm

/-- Forgetting the differential on curved right modules is left adjoint to coinduction `N ↦ G⁻ N`.
-/
noncomputable def forgetDifferentialCoinducedAdj (h : IsCurvedDGAlgebra 𝒜 d w) :
    forgetDifferential (h := h) ⊣ coinduced h :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun f := coinducedLift (M := ForgetEnrichment.to _ M) f
          invFun g := (forgetDifferential (h := h)).map (Y := (coinduced h).obj N) g ≫
            coinducedFst h N
          left_inv f := forgetDifferential_map_coinducedLift_comp_coinducedFst
            (M := ForgetEnrichment.to _ M) f
          right_inv g := coinducedLift_forgetDifferential_map_comp_coinducedFst
            (M := ForgetEnrichment.to _ M) g }
      homEquiv_naturality_left_symm _ _ := by simp
      homEquiv_naturality_right {M _ N₂} _ _ := by
        dsimp only [coinduced]
        exact closedHom_ext (M := ForgetEnrichment.to _ M) fun m ↦
          (coinducedEquiv h N₂).injective (by simp) }

/-- The forward adjunct of `forgetDifferentialCoinducedAdj` is `coinducedLift`. -/
@[simp]
theorem forgetDifferentialCoinducedAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (f : toGradedModuleCat M ⟶ N) :
    (forgetDifferentialCoinducedAdj h).homEquiv
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) N f = coinducedLift f := by
  rw [forgetDifferentialCoinducedAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl

/-- The reverse adjunct of `forgetDifferentialCoinducedAdj` projects along `coinducedFst`. -/
@[simp]
theorem forgetDifferentialCoinducedAdj_homEquiv_symm_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (g : M ⟶ (coinduced h).obj N) :
    ((forgetDifferentialCoinducedAdj h).homEquiv M N).symm g =
      (forgetDifferential (h := h)).map g ≫ coinducedFst h N := by
  rw [forgetDifferentialCoinducedAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl

/-- The unit of `forgetDifferentialCoinducedAdj` at `M` is
`coinducedLift (𝟙 (toGradedModuleCat M))`. -/
@[simp]
theorem forgetDifferentialCoinducedAdj_unit_app_of (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (forgetDifferentialCoinducedAdj h).unit.app
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
        coinducedLift (𝟙 (toGradedModuleCat M)) := by
  rw [forgetDifferentialCoinducedAdj, Adjunction.mkOfHomEquiv_unit_app, Equiv.coe_fn_mk]; rfl

/-- The counit of `forgetDifferentialCoinducedAdj` at `N` is `coinducedFst h N`. -/
@[simp]
theorem forgetDifferentialCoinducedAdj_counit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (forgetDifferentialCoinducedAdj h).counit.app N = coinducedFst h N := by
  rw [forgetDifferentialCoinducedAdj, Adjunction.mkOfHomEquiv_counit_app, Equiv.coe_fn_symm_mk,
    CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- Every coinduced curved right module `G⁻ N` is contractible, hence zero in the curved homotopy
category. -/
theorem isZero_homotopy_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h N)) :=
  isZero_homotopy_inducedObj h (N.shiftObj (-1))

/-- For an injective graded right module `I`, `G⁻ I` is graded-injective. -/
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
    rw [InternalGrading.ofDecomposition_piece]; infer_instance
  obtain ⟨I⟩ := @EnoughInjectives.presentation _ _
    GradedModuleCat.enoughInjectives.{u, u, u} (toGradedModuleCat M)
  exact ⟨I.J, inferInstance, (forgetDifferentialCoinducedAdj h).homEquiv
    (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f, inferInstance⟩

end Functor

end TauCeti.CurvedDGRightModuleCat

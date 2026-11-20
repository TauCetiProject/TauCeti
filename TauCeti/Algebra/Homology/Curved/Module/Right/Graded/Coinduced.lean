/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Coinduced curved right modules from graded right modules

Dual to the free curved module functor `G⁺`, every graded right module $N$ over a curved
differential graded algebra $(A, d, w)$ gives rise to a coinduced curved right module $G^- N$.
Up to swapping the two summands of $N \oplus N$, $G^- N$ coincides with
`freeObj h (N.shiftObj (-1))` ($G^+(N\{-1\})$): over the ground ring its underlying module is
$N \oplus N$, graded with degree-$p$ piece $N_p \oplus N_{p + 1}$, its twisted right $A$-action is
$$(x, y) \cdot a = (x \cdot a,\ y \cdot a + (-1)^{|x|} x \cdot d a),$$ and its curved
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

/-- The **coinduced curved right module** `G⁻ N` associated to a graded right module `N`, realized
as `freeObj h (N.shiftObj (-1))`. Over `R` its carrier is `N × N` with degree-`p` piece
`N_p × N_{p + 1}`, twisted right action `(x, y) · a = (x · a, y · a + (-1)^{|x|} x · d a)`, and
differential `(x, y) ↦ (y, x · w)`. -/
noncomputable abbrev coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uN} h :=
  freeObj h (N.shiftObj (-1))

/-- The natural graded right-module inclusion `N{-1} ⟶ U(G⁻ N)` sending `y` to `(0, y)`. -/
noncomputable def coinducedInr (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h N) :=
  freeUnit h (N.shiftObj (-1))

/-- The natural graded right-module projection `U(G⁻ N) ⟶ N` sending `(x, y)` to `x`. -/
noncomputable def coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  freeProj h (N.shiftObj (-1)) ≫
    GradedModuleCat.ofHom LinearMap.id (LinearMap.isHomogeneous_def.mpr fun p _ hx ↦ by
      rw [GradedModuleCat.mem_shiftObj_piece_iff, GradedModuleCat.mem_shiftObj_piece_iff] at hx
      simpa only [LinearMap.id_apply, sub_neg_eq_add, add_zero, sub_add_cancel] using hx)

private theorem freeProj_freeι (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (y : N) :
    (freeProj h (N.shiftObj (-1))).hom (freeι h (N.shiftObj (-1)) y) = 0 := by
  have h0 := congrArg (fun φ : N.shiftObj (-1) ⟶ (N.shiftObj (-1)).shiftObj 1 ↦ φ.hom y)
    (freeUnit_comp_freeProj h (N.shiftObj (-1)))
  simpa only [GradedModuleCat.hom_comp, LinearMap.comp_apply, hom_freeUnit,
    GradedModuleCat.hom_zero, LinearMap.zero_apply] using h0

private theorem freeProj_differential_differential_freeι (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (x : N) :
    (freeProj h (N.shiftObj (-1))).hom
        ((coinducedObj h N).differential
          ((coinducedObj h N).differential (freeι h (N.shiftObj (-1)) x))) = 0 := by
  rw [(coinducedObj h N).isCurvedDGRightModule.sq_eq, LinearMap.map_smul, freeProj_freeι, smul_zero]

private theorem coinducedFst_smul_base (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (r : R) (z : coinducedObj h N) :
    (coinducedFst h N).hom (r • z) = r • (coinducedFst h N).hom z := by
  rw [← algebraMap_smul Aᵐᵒᵖ r z, (coinducedFst h N).hom.map_smul, algebraMap_smul]

/-- The `R`-linear equivalence identifying the carrier of `coinducedObj h N` with `N × N`. -/
noncomputable def coinducedEquiv (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h N ≃ₗ[R] N × N where
  toFun z := ((coinducedFst h N).hom z, (coinducedFst h N).hom ((coinducedObj h N).differential z))
  invFun p := freeι h (N.shiftObj (-1)) p.2 +
    (coinducedObj h N).differential (freeι h (N.shiftObj (-1)) p.1)
  map_add' _ _ := Prod.ext (map_add _ _ _)
    (by dsimp only; rw [map_add, map_add]; rfl)
  map_smul' r z := Prod.ext (coinducedFst_smul_base h N r z)
    (by
      dsimp only
      rw [LinearMap.map_smul, coinducedFst_smul_base, RingHom.id_apply, Prod.smul_snd])
  left_inv z := by
    obtain ⟨u, v, hz⟩ := exists_eq_freeι_add_differential_freeι h (N.shiftObj (-1)) z
    have h1 : (coinducedFst h N).hom z = v := by
      rw [hz, coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom, LinearMap.id_comp,
        map_add, freeProj_freeι, freeProj_differential_freeι_apply, zero_add]
    have h2 : (coinducedFst h N).hom ((coinducedObj h N).differential z) = u := by
      rw [hz, coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom, LinearMap.id_comp,
        map_add, map_add, freeProj_differential_freeι_apply,
        freeProj_differential_differential_freeι, add_zero]
    dsimp only
    rw [h1, h2]
    exact hz.symm
  right_inv p := by
    refine Prod.ext ?_ ?_
    · change (freeProj h (N.shiftObj (-1))).hom (freeι h (N.shiftObj (-1)) p.2 +
        (coinducedObj h N).differential (freeι h (N.shiftObj (-1)) p.1)) = p.1
      rw [map_add, freeProj_freeι, freeProj_differential_freeι_apply, zero_add]
    · change (freeProj h (N.shiftObj (-1))).hom ((coinducedObj h N).differential
        (freeι h (N.shiftObj (-1)) p.2 +
          (coinducedObj h N).differential (freeι h (N.shiftObj (-1)) p.1))) = p.2
      rw [map_add, map_add, freeProj_differential_freeι_apply,
        freeProj_differential_differential_freeι, add_zero]

private theorem coinducedEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N z =
      ((coinducedFst h N).hom z, (coinducedFst h N).hom ((coinducedObj h N).differential z)) := by
  rw [coinducedEquiv]; rfl

/-- Elements of `coinducedObj h N` are determined by their two components in `N × N`. -/
@[ext]
theorem coinducedObj_ext {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {z₁ z₂ : coinducedObj h N} (h₁ : (coinducedEquiv h N z₁).1 = (coinducedEquiv h N z₂).1)
    (h₂ : (coinducedEquiv h N z₁).2 = (coinducedEquiv h N z₂).2) : z₁ = z₂ :=
  (coinducedEquiv h N).injective (Prod.ext h₁ h₂)

/-- The graded projection `coinducedFst` extracts the first component in `N × N`. -/
@[simp]
theorem coinducedFst_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) : (coinducedFst h N).hom z = (coinducedEquiv h N z).1 := by
  rw [coinducedEquiv_apply]

/-- The graded inclusion `coinducedInr` sends `y` to `(0, y)` in `N × N`. -/
@[simp]
theorem coinducedEquiv_coinducedInr_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (y : N) :
    coinducedEquiv h N ((coinducedInr h N).hom y) = (0, y) := by
  rw [coinducedEquiv_apply]
  refine Prod.ext ?_ ?_
  · rw [coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom, LinearMap.id_comp,
      coinducedInr, hom_freeUnit]
    exact freeProj_freeι h N y
  · rw [coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom, LinearMap.id_comp,
      coinducedInr, hom_freeUnit]
    exact freeProj_differential_freeι_apply h (N.shiftObj (-1)) y

/-- The curved differential on `coinducedObj h N` sends `(x, y)` to `(y, x · w)`. -/
@[simp]
theorem coinducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N ((coinducedObj h N).differential z) =
      ((coinducedEquiv h N z).2, op w • (coinducedEquiv h N z).1) := by
  rw [coinducedEquiv_apply, coinducedEquiv_apply]
  refine Prod.ext rfl ?_
  rw [(coinducedObj h N).isCurvedDGRightModule.sq_eq, (coinducedFst h N).hom.map_smul]

/-- An element of `coinducedObj h N` has degree `p` iff its components lie in `N_p` and `N_{p + 1}`.
-/
@[simp]
theorem mem_coinducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : coinducedObj h N} :
    z ∈ (coinducedObj h N).grading p ↔ (coinducedEquiv h N z).1 ∈ N.grading.piece p ∧
      (coinducedEquiv h N z).2 ∈ N.grading.piece (p + 1) := by
  refine ⟨fun hz ↦ ⟨?_, ?_⟩, fun ⟨hx, hy⟩ ↦ ?_⟩
  · rw [← toGradedModuleCat_piece] at hz
    simpa only [← coinducedFst_apply, add_zero] using GradedModuleCat.map_mem (coinducedFst h N) hz
  · have hdz : (coinducedObj h N).differential z ∈ (coinducedObj h N).grading (p + 1) :=
      (coinducedObj h N).isCurvedDGRightModule.isHomogeneous.map_mem hz
    rw [← toGradedModuleCat_piece] at hdz
    have hmem :
        (coinducedFst h N).hom ((coinducedObj h N).differential z) ∈ N.grading.piece (p + 1) := by
      simpa only [add_zero] using GradedModuleCat.map_mem (coinducedFst h N) hdz
    rw [coinducedEquiv_apply]; exact hmem
  · rw [← (coinducedEquiv h N).symm_apply_apply z]
    change freeι h (N.shiftObj (-1)) (coinducedEquiv h N z).2 +
        (coinducedObj h N).differential (freeι h (N.shiftObj (-1)) (coinducedEquiv h N z).1) ∈
      (coinducedObj h N).grading p
    have hy' : (coinducedEquiv h N z).2 ∈ (N.shiftObj (-1)).grading.piece p := by
      rw [GradedModuleCat.mem_shiftObj_piece_iff]; simpa only [sub_neg_eq_add] using hy
    have hx' : (coinducedEquiv h N z).1 ∈ (N.shiftObj (-1)).grading.piece (p - 1) := by
      rw [GradedModuleCat.mem_shiftObj_piece_iff]
      simpa only [sub_neg_eq_add, sub_add_cancel] using hx
    have h1 :
        freeι h (N.shiftObj (-1)) (coinducedEquiv h N z).2 ∈ (coinducedObj h N).grading p := by
      rw [← toGradedModuleCat_piece]
      simpa only [hom_freeUnit, add_zero] using
        GradedModuleCat.map_mem (freeUnit h (N.shiftObj (-1))) hy'
    have h2' : freeι h (N.shiftObj (-1)) (coinducedEquiv h N z).1 ∈
        (coinducedObj h N).grading (p - 1) := by
      rw [← toGradedModuleCat_piece]
      simpa only [hom_freeUnit, add_zero] using
        GradedModuleCat.map_mem (freeUnit h (N.shiftObj (-1))) hx'
    have h2 : (coinducedObj h N).differential (freeι h (N.shiftObj (-1)) (coinducedEquiv h N z).1) ∈
        (coinducedObj h N).grading p := by
      simpa only [sub_add_cancel] using
        (coinducedObj h N).isCurvedDGRightModule.isHomogeneous.map_mem h2'
    exact Submodule.add_mem _ h1 h2

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `coinducedObj h N`, expressed in `N × N`. -/
@[simp]
theorem coinducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : coinducedObj h N) :
    coinducedEquiv h N (a • z) = (a • (coinducedEquiv h N z).1,
      a • (coinducedEquiv h N z).2 +
        op (d a.unop) • N.grading.koszulTwist 1 (coinducedEquiv h N z).1) := by
  refine Prod.ext ?_ ?_
  · rw [← coinducedFst_apply, (coinducedFst h N).hom.map_smul, coinducedFst_apply]
  · rw [coinducedEquiv_apply, coinducedEquiv_apply]
    dsimp only
    rw [(coinducedObj h N).differential_smul, map_add, (coinducedFst h N).hom.map_smul,
      (coinducedFst h N).hom.map_smul]
    congr 2
    let f' : toGradedModuleCat (coinducedObj h N) ⟶ N := coinducedFst h N
    have hf' : LinearMap.IsHomogeneous (f'.hom.restrictScalars R)
        (InternalGrading.ofDecomposition (coinducedObj h N).grading).piece N.grading.piece 0 :=
      LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        rw [InternalGrading.ofDecomposition_piece, ← toGradedModuleCat_piece] at hx
        simpa only [LinearMap.restrictScalars_apply, add_zero] using
          GradedModuleCat.map_mem f' hx
    have htw := hf'.koszulTwist_apply 1 z
    simp only [LinearMap.restrictScalars_apply, one_mul, Int.negOnePow_zero, Units.val_one,
      Int.cast_one, one_smul] at htw
    exact htw.symm

/-! ### Graded short exact sequence and injectivity -/

/-- The graded inclusion of `N{-1}` into `G⁻ N` followed by `coinducedFst` vanishes. -/
@[reassoc (attr := simp)]
theorem coinducedInr_comp_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedInr h N ≫ coinducedFst h N = 0 := by
  ext y
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.hom_zero,
    LinearMap.zero_apply, coinducedFst_apply, coinducedEquiv_coinducedInr_apply]

/-- After forgetting the differential, `G⁻ N` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ U(G⁻ N) ⟶ N ⟶ 0` of graded right modules. -/
theorem shortExact_coinducedInr_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedInr h N) (coinducedFst h N)
      (coinducedInr_comp_coinducedFst h N)).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).2 fun _ _ hy ↦ by
    have h2 := congrArg (fun z : coinducedObj h N ↦ (coinducedEquiv h N z).2) hy
    dsimp only at h2
    rwa [coinducedEquiv_coinducedInr_apply, coinducedEquiv_coinducedInr_apply] at h2
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

/-! ### Functoriality, adjunction, and closed monomorphisms into graded-injectives -/

section Functor

open CategoryTheory CategoryTheory.Limits MulOpposite

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- The **coinduction functor** `N ↦ G⁻ N` from graded right modules to curved right modules with
closed degree-zero morphisms, realized as `N ↦ G⁺(N{-1})`. -/
@[expose, implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) :=
  GradedModuleCat.shiftFunctor (-1) ⋙ freeFunctor

/-- The coinduction functor sends a graded right module `N` to `coinducedObj h N`. -/
@[simp]
theorem coinduced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

private theorem coinducedFst_closedHom_coinduced_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    (coinducedFst h N₂).hom (closedHom ((coinduced h).map f) z) =
      f.hom ((coinducedFst h N₁).hom z) := by
  let g : N₁.shiftObj (-1) ⟶ N₂.shiftObj (-1) := (GradedModuleCat.shiftFunctor (-1)).map f
  have hmap : (coinduced h).map f = freeDesc (g ≫ freeUnit h (N₂.shiftObj (-1))) := rfl
  obtain ⟨u, v, hz⟩ := exists_eq_freeι_add_differential_freeι h (N₁.shiftObj (-1)) z
  have lhs_eq : (coinducedFst h N₂).hom (closedHom ((coinduced h).map f) z) = f.hom v := by
    rw [hz, map_add, map_add, hmap, closedHom_freeDesc_freeι_apply,
      closedHom_freeDesc_differential_freeι_apply]
    have hgu : (g ≫ freeUnit h (N₂.shiftObj (-1))).hom u =
        freeι h (N₂.shiftObj (-1)) (f.hom u) := by
      rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, hom_freeUnit]
      rfl
    have hgv : (g ≫ freeUnit h (N₂.shiftObj (-1))).hom v =
        freeι h (N₂.shiftObj (-1)) (f.hom v) := by
      rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, hom_freeUnit]
      rfl
    rw [hgu, hgv, coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom,
      LinearMap.id_comp]
    change (freeProj h (N₂.shiftObj (-1))).hom (freeι h (N₂.shiftObj (-1)) (f.hom u)) +
        (freeProj h (N₂.shiftObj (-1))).hom
          ((freeObj h (N₂.shiftObj (-1))).differential
            (freeι h (N₂.shiftObj (-1)) (f.hom v))) = f.hom v
    rw [freeProj_freeι, freeProj_differential_freeι_apply, zero_add]
  have rhs_eq : (coinducedFst h N₁).hom z = v := by
    rw [hz, coinducedFst, GradedModuleCat.hom_comp, GradedModuleCat.hom_ofHom, LinearMap.id_comp,
      map_add, freeProj_freeι, freeProj_differential_freeι_apply, zero_add]
  rw [lhs_eq, rhs_eq]

/-- On underlying pairs in `N × N`, `(coinduced h).map f` applies `f` componentwise. -/
@[simp]
theorem coinducedEquiv_closedHom_coinduced_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    coinducedEquiv h N₂ (closedHom ((coinduced h).map f) z) =
      (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2) := by
  refine Prod.ext ?_ ?_
  · rw [← coinducedFst_apply, ← coinducedFst_apply]
    exact coinducedFst_closedHom_coinduced_map_apply h f z
  · change (coinducedFst h N₂).hom ((coinducedObj h N₂).differential
        (closedHom ((coinduced h).map f) z)) =
      f.hom ((coinducedFst h N₁).hom ((coinducedObj h N₁).differential z))
    rw [differential_closedHom]
    exact coinducedFst_closedHom_coinduced_map_apply h f ((coinducedObj h N₁).differential z)

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Additive :=
  inferInstanceAs (GradedModuleCat.shiftFunctor (-1) ⋙ freeFunctor).Additive

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Linear R :=
  inferInstanceAs ((GradedModuleCat.shiftFunctor (-1) ⋙ freeFunctor).Linear R)

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
      homEquiv_naturality_right {M _ N₂} _ _ :=
        closedHom_ext (M := ForgetEnrichment.to _ M) (N := coinducedObj h N₂) fun m ↦
          (coinducedEquiv h N₂).injective <| by
            simp only [Equiv.coe_fn_mk, closedHom_comp, LinearMap.comp_apply]
            rw [coinducedEquiv_closedHom_coinduced_map_apply,
              coinducedEquiv_closedHom_coinducedLift_apply]
            simp }

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
  isZero_homotopy_freeObj h (N.shiftObj (-1))

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
  have hmono : Mono ((forgetDifferentialCoinducedAdj h).homEquiv
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f) := by
    have : Mono ((forgetDifferential (h := h)).map
        ((forgetDifferentialCoinducedAdj h).homEquiv
          (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f) ≫
        coinducedFst h I.J) := by
      simpa only [forgetDifferentialCoinducedAdj_homEquiv_apply,
        forgetDifferential_map_coinducedLift_comp_coinducedFst] using I.mono
    have : Mono ((forgetDifferential (h := h)).map ((forgetDifferentialCoinducedAdj h).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f)) :=
      mono_of_mono _ (coinducedFst h I.J)
    exact (forgetDifferential (h := h)).mono_of_mono_map this
  exact ⟨I.J, inferInstance, (forgetDifferentialCoinducedAdj h).homEquiv
    (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f, hmono⟩

end Functor

end TauCeti.CurvedDGRightModuleCat

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
contractible in the curved homotopy category (`isZero_homotopy_coinducedObj`, via
`isZero_homotopy_freeObj h (N.shiftObj (-1))`) and sits in a graded short exact sequence
$0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$. Thus $G^- I$
is graded-injective when $I$ is injective, giving closed monomorphisms into contractible
graded-injectives.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj` and `TauCeti.CurvedDGRightModuleCat.coinducedEquiv`:
  the coinduced curved right module $G^- N$ and its carrier equivalence with $N \times N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedInr` and
  `TauCeti.CurvedDGRightModuleCat.coinducedFst`: the graded inclusion
  $N\{-1\} \longrightarrow U(G^- N)$ and projection $U(G^- N) \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.coinduced`, `TauCeti.CurvedDGRightModuleCat.coinducedIso`,
  `TauCeti.CurvedDGRightModuleCat.coinducedLift`, and
  `TauCeti.CurvedDGRightModuleCat.forgetDifferentialCoinducedAdj`: the right-adjoint functor,
  its comparison isomorphism with `shiftFunctor (-1) ⋙ freeFunctor`, adjunct closed morphism, and
  adjunction with forgetting the differential.

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
internally as `freeObj h (N.shiftObj (-1))`. Over `R` its carrier is `N × N` with degree-`p`
piece `N_p × N_{p + 1}`, twisted right action `(x, y) · a = (x · a, y · a + (-1)^{|x|} x · d a)`,
and differential `(x, y) ↦ (y, x · w)`. -/
noncomputable def coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uN} h :=
  freeObj h (N.shiftObj (-1))

private noncomputable def shiftNegOneOneIso
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (N.shiftObj (-1)).shiftObj 1 ≅ N :=
  GradedModuleCat.isoMk (LinearEquiv.refl Aᵐᵒᵖ N) fun p _ ↦ by
    rw [GradedModuleCat.mem_shiftObj_piece_iff, GradedModuleCat.mem_shiftObj_piece_iff]
    have hp : p - 1 - -1 = p := by omega
    rw [hp, LinearEquiv.refl_apply]

private theorem hom_shiftNegOneOneIso_hom
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (shiftNegOneOneIso N).hom.hom = LinearMap.id :=
  (rfl)

/-- The canonical graded right-linear inclusion `N{-1} ⟶ U(G⁻ N)`. -/
noncomputable def coinducedInr (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h N) :=
  freeUnit h (N.shiftObj (-1))

/-- The natural graded right-module projection `U(G⁻ N) ⟶ N` sending `(x, y)` to `x`. -/
noncomputable def coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  freeProj h (N.shiftObj (-1)) ≫ (shiftNegOneOneIso N).hom

/-- The `R`-linear equivalence identifying the carrier of `coinducedObj h N` with `N × N`. -/
noncomputable def coinducedEquiv (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h N ≃ₗ[R] N × N :=
  (freeEquiv h (N.shiftObj (-1))).trans (LinearEquiv.prodComm R N N)

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
  let z' : freeObj h (N.shiftObj (-1)) := z
  change (shiftNegOneOneIso N).hom.hom ((freeProj h (N.shiftObj (-1))).hom z') =
    (LinearEquiv.prodComm R N N (freeEquiv h (N.shiftObj (-1)) z')).1
  rw [hom_shiftNegOneOneIso_hom, LinearMap.id_apply, freeProj_apply, LinearEquiv.prodComm_apply]
  rfl

/-- Evaluating `coinducedEquiv` on the inclusion `coinducedInr h N` gives `(0, y)`. -/
@[simp]
theorem coinducedEquiv_coinducedInr (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (y : N) :
    coinducedEquiv h N ((coinducedInr h N).hom y) = (0, y) := by
  change (LinearEquiv.prodComm R N N)
      (freeEquiv h (N.shiftObj (-1)) ((freeUnit h (N.shiftObj (-1))).hom y)) = (0, y)
  rw [hom_freeUnit, freeEquiv_freeι, LinearEquiv.prodComm_apply]
  rfl

/-- The curved differential on `coinducedObj h N` sends `(x, y)` to `(y, x · w)`. -/
@[simp]
theorem coinducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N ((coinducedObj h N).differential z) =
      ((coinducedEquiv h N z).2, op w • (coinducedEquiv h N z).1) := by
  let z' : freeObj h (N.shiftObj (-1)) := z
  change (LinearEquiv.prodComm R N N)
      (freeEquiv h (N.shiftObj (-1)) ((freeObj h (N.shiftObj (-1))).differential z')) =
    ((LinearEquiv.prodComm R N N (freeEquiv h (N.shiftObj (-1)) z')).2,
      op w • (LinearEquiv.prodComm R N N (freeEquiv h (N.shiftObj (-1)) z')).1)
  rw [freeEquiv_differential]
  simp only [LinearEquiv.prodComm_apply]
  rfl

private theorem coinducedEquiv_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    (coinducedEquiv h N z).2 = (coinducedFst h N).hom ((coinducedObj h N).differential z) := by
  rw [coinducedFst_apply, coinducedEquiv_differential]

/-- An element of `coinducedObj h N` has degree `p` iff its components lie in `N_p` and `N_{p + 1}`.
-/
@[simp]
theorem mem_coinducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : coinducedObj h N} :
    z ∈ (coinducedObj h N).grading p ↔ (coinducedEquiv h N z).1 ∈ N.grading.piece p ∧
      (coinducedEquiv h N z).2 ∈ N.grading.piece (p + 1) := by
  let z' : freeObj h (N.shiftObj (-1)) := z
  have hfree := mem_freeObj_grading_iff h (N.shiftObj (-1)) (p := p) (x := z')
  refine hfree.trans ?_
  rw [GradedModuleCat.mem_shiftObj_piece_iff, GradedModuleCat.mem_shiftObj_piece_iff]
  change (freeEquiv h (N.shiftObj (-1)) z').1 ∈ N.grading.piece (p - -1) ∧
      (freeEquiv h (N.shiftObj (-1)) z').2 ∈ N.grading.piece (p - 1 - -1) ↔
    (LinearEquiv.prodComm R N N (freeEquiv h (N.shiftObj (-1)) z')).1 ∈ N.grading.piece p ∧
      (LinearEquiv.prodComm R N N (freeEquiv h (N.shiftObj (-1)) z')).2 ∈ N.grading.piece (p + 1)
  simp [sub_neg_eq_add, sub_add_cancel, and_comm]

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `coinducedObj h N`, expressed in `N × N`. -/
@[simp]
theorem coinducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : coinducedObj h N) :
    coinducedEquiv h N (a • z) = (a • (coinducedEquiv h N z).1,
      a • (coinducedEquiv h N z).2 +
        op (d a.unop) • N.grading.koszulTwist 1 (coinducedEquiv h N z).1) := by
  refine Prod.ext
    (by rw [← coinducedFst_apply, (coinducedFst h N).hom.map_smul, coinducedFst_apply]) ?_
  dsimp only
  rw [coinducedEquiv_snd, coinducedEquiv_snd, (coinducedObj h N).differential_smul, map_add,
    (coinducedFst h N).hom.map_smul, (coinducedFst h N).hom.map_smul, ← toGradedModuleCat_grading,
    ← GradedModuleCat.koszulTwist_hom_apply]
  simp [coinducedFst_apply]

/-! ### Graded short exact sequence and injectivity -/

/-- The graded inclusion of `N{-1}` into `G⁻ N` followed by `coinducedFst` vanishes. -/
@[reassoc (attr := simp)]
theorem coinducedInr_comp_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedInr h N ≫ coinducedFst h N = 0 := by
  rw [coinducedInr, coinducedFst]
  dsimp only [coinducedObj]
  rw [← Category.assoc, freeUnit_comp_freeProj, Limits.zero_comp]

/-- After forgetting the differential, `G⁻ N` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ U(G⁻ N) ⟶ N ⟶ 0` of graded right modules. -/
theorem shortExact_coinducedInr_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedInr h N) (coinducedFst h N)
      (coinducedInr_comp_coinducedFst h N)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk
      (S₁ := ShortComplex.mk (freeUnit h (N.shiftObj (-1))) (freeProj h (N.shiftObj (-1)))
        (freeUnit_comp_freeProj h (N.shiftObj (-1))))
      (Iso.refl _) (Iso.refl _) (shiftNegOneOneIso N)
      (by simp [coinducedInr, coinducedObj]) (by simp [coinducedFst, coinducedObj]))
    (freeShortExact h (N.shiftObj (-1)))

/-- If `I` is an injective graded right module, `U(G⁻ I)` is injective. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (coinducedObj h I)) := by
  have : Injective (I.shiftObj (-1)) := GradedModuleCat.injective_shiftObj I (-1)
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((shortExact_coinducedInr_coinducedFst h I).hasInjectiveDimensionLT_X₂ 1 inferInstance
      inferInstance)

end CoinducedObj

/-! ### Functoriality, contractibility, adjunction, and graded-injective presentations -/

section Functor

open CategoryTheory CategoryTheory.Limits MulOpposite

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Every coinduced curved right module `coinducedObj h N` is contractible in the curved
homotopy category. -/
theorem isZero_homotopy_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h N)) :=
  isZero_homotopy_freeObj h (N.shiftObj (-1))

/-- Sealed morphism action of `coinduced`, keeping the shifted-free implementation encapsulated. -/
noncomputable def coinducedMap (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₁) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₂) :=
  (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map f)

/-- The **coinduction functor** `N ↦ G⁻ N` from graded right modules to curved right modules with
closed degree-zero morphisms. Its object map computes during type inference, matching
`forgetDifferential`, while `coinducedObj` and `coinducedMap` remain sealed. -/
@[expose, implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)
  map f := coinducedMap h f
  map_id N := by
    change (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map (𝟙 N)) = _
    simp only [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    rw [coinducedMap, coinducedMap, coinducedMap, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp]
    rfl

/-- The coinduction functor sends a graded right module `N` to `coinducedObj h N`. -/
@[simp]
theorem coinduced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

/-- Comparison isomorphism identifying the sealed coinduction functor with
`GradedModuleCat.shiftFunctor (-1) ⋙ freeFunctor`. -/
noncomputable def coinducedIso (h : IsCurvedDGAlgebra 𝒜 d w) :
    coinduced h ≅ GradedModuleCat.shiftFunctor (-1) ⋙ freeFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp only [coinduced, coinducedMap, Functor.comp_obj, Functor.comp_map, Iso.refl_hom,
      coinducedObj]
    rw [Category.comp_id, Category.id_comp])

/-- Under `coinducedIso`, the carrier pair `(x, y)` in `coinducedObj h N` swaps to `(y, x)` in
`freeObj h (N.shiftObj (-1))`. -/
theorem freeEquiv_closedHom_coinducedIso_hom_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    freeEquiv h (N.shiftObj (-1)) (closedHom ((coinducedIso h).hom.app N) z) =
      (coinducedEquiv h N z).swap := by
  have hid : closedHom ((coinducedIso h).hom.app N) z = z :=
    LinearMap.congr_fun (closedHom_id _) z
  rw [hid, coinducedEquiv]
  rfl

/-- Under `(coinducedIso h).inv`, the carrier pair `(y, x)` in `freeObj h (N.shiftObj (-1))`
swaps to `(x, y)` in `coinducedObj h N`. -/
theorem coinducedEquiv_closedHom_coinducedIso_inv_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : freeObj h (N.shiftObj (-1))) :
    coinducedEquiv h N (closedHom ((coinducedIso h).inv.app N) z) =
      (freeEquiv h (N.shiftObj (-1)) z).swap := by
  have hid : closedHom ((coinducedIso h).inv.app N) z = z :=
    LinearMap.congr_fun (closedHom_id _) z
  rw [hid, coinducedEquiv]
  rfl

private theorem freeProj_closedHom_freeFunctor_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {V₁ V₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : V₁ ⟶ V₂) (z : freeObj h V₁) :
    (freeProj h V₂).hom (closedHom ((freeFunctor (h := h)).map f) z) =
      f.hom ((freeProj h V₁).hom z) := by
  have hgen (x : V₁) :
      closedHom ((freeFunctor (h := h)).map f) (freeι h V₁ x) = freeι h V₂ (f.hom x) := by
    rw [freeFunctor_map, closedHom_freeDesc_freeι_apply, GradedModuleCat.hom_comp,
      LinearMap.comp_apply, hom_freeUnit]
  obtain ⟨u, v, rfl⟩ := exists_eq_freeι_add_differential_freeι h V₁ z
  have hd :
      closedHom ((freeFunctor (h := h)).map f) ((freeObj h V₁).differential (freeι h V₁ v)) =
        (freeObj h V₂).differential (freeι h V₂ (f.hom v)) := by
    -- Identify `((freeFunctor.obj _).differential)` with `(freeObj h _).differential`.
    change closedHom ((freeFunctor (h := h)).map f)
        (((freeFunctor (h := h)).obj V₁).differential (freeι h V₁ v)) =
      ((freeFunctor (h := h)).obj V₂).differential (freeι h V₂ (f.hom v))
    rw [← differential_closedHom, hgen v]
  rw [map_add, hgen u, hd, map_add, map_add, freeProj_apply, freeEquiv_freeι,
    freeProj_differential_freeι_apply, freeProj_apply, freeEquiv_freeι,
    freeProj_differential_freeι_apply]
  simp

private theorem coinducedFst_closedHom_coinduced_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    (coinducedFst h N₂).hom (closedHom ((coinduced h).map f) z) =
      f.hom ((coinducedFst h N₁).hom z) := by
  -- Cross the sealed `coinducedObj` wrapper to apply `freeProj_closedHom_freeFunctor_map_apply`.
  let z' : freeObj h (N₁.shiftObj (-1)) := z
  change (shiftNegOneOneIso N₂).hom.hom ((freeProj h (N₂.shiftObj (-1))).hom
      (closedHom ((freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map f)) z')) =
    f.hom ((shiftNegOneOneIso N₁).hom.hom ((freeProj h (N₁.shiftObj (-1))).hom z'))
  rw [hom_shiftNegOneOneIso_hom, hom_shiftNegOneOneIso_hom, LinearMap.id_apply, LinearMap.id_apply,
    freeProj_closedHom_freeFunctor_map_apply, GradedModuleCat.hom_shiftFunctor_map]
  rfl

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
  · rw [coinducedEquiv_snd, coinducedEquiv_snd, differential_closedHom]
    exact coinducedFst_closedHom_coinduced_map_apply h f ((coinducedObj h N₁).differential z)

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Additive where
  map_add {X Y f g} := by
    change (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map (f + g)) =
      (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map f) +
        (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map g)
    simp

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).Linear R where
  map_smul {X Y} f r := by
    change (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map (r • f)) =
      r • (freeFunctor (h := h)).map ((GradedModuleCat.shiftFunctor (-1)).map f)
    simp

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
          rw [← toGradedModuleCat_grading]
          exact GradedModuleCat.koszulTwist_hom_apply f 1 m
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
  rw [coinducedEquiv_differential] at hd
  dsimp only at hd
  exact Prod.ext (coinducedFst_apply h N _) ((coinducedFst_apply h N _).trans hd.symm)

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

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (forgetDifferential (h := h)).IsLeftAdjoint :=
  (forgetDifferentialCoinducedAdj h).isLeftAdjoint

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (coinduced h).IsRightAdjoint :=
  (forgetDifferentialCoinducedAdj h).isRightAdjoint

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
  obtain ⟨I⟩ := EnoughInjectives.presentation (toGradedModuleCat M)
  exact ⟨I.J, inferInstance, (forgetDifferentialCoinducedAdj h).homEquiv
    (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) I.J I.f, inferInstance⟩

end Functor

end TauCeti.CurvedDGRightModuleCat

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Diffeology.DSmoothMap
public import TauCeti.Geometry.Diffeology.Manifold

/-!
# Bundled manifold maps and diffeological mapping spaces

This file bridges Mathlib's bundled smooth manifold maps (`ContMDiffMap`, denoted `C^∞⟮I, M; J, N⟯`)
and manifold diffeomorphisms (`Diffeomorph`, denoted `M ≃ₘ^∞⟮I, J⟯ N`) with bundled diffeologically
smooth maps (`TauCeti.Diffeology.DSmoothMap`) and diffeological diffeomorphisms
(`TauCeti.Diffeology.DSmoothEquiv`):

* `ContMDiffMap.toDSmoothMap` views any smooth manifold map between manifold-compatible diffeologies
  as a `DSmoothMap`, without finite-dimensionality or smooth-atlas hypotheses.
* When the source `M` is a finite-dimensional boundaryless smooth manifold,
  `TauCeti.Diffeology.DSmoothMap.equivContMDiffMap` identifies `DSmoothMap M N` with
  `C^∞⟮I, M; J, N⟯`.
* `Diffeomorph.toDSmoothEquiv` views any smooth manifold diffeomorphism between compatible
  diffeologies as a `DSmoothEquiv`, and `TauCeti.Diffeology.DSmoothEquiv.equivDiffeomorph`
  identifies `DSmoothEquiv M N` with `M ≃ₘ^∞⟮I, J⟯ N` when both `M` and `N` are finite-dimensional
  boundaryless smooth manifolds.
* For charted spaces with smooth multiplication (`ContMDiffMul I ∞ G`) and compatible diffeology,
  multiplication is diffeologically smooth (`TauCeti.dSmooth_mul`), so left and right translation
  `g ↦ (smoothLeftMul I g).toDSmoothMap` and `g ↦ (smoothRightMul I g).toDSmoothMap` are smooth
  maps `G → DSmoothMap G G` for the functional diffeology.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 4, for manifolds and their mapping spaces in diffeology.
-/

public noncomputable section

open Function Set Diffeology TauCeti
open scoped Manifold ContDiff

section ContMDiffMapBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [DiffeologicalSpace M] [IsContMDiffCompatible I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [DiffeologicalSpace N] [IsContMDiffCompatible J N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [DiffeologicalSpace P] [IsContMDiffCompatible K P]

namespace ContMDiffMap

/-- View a bundled `C^∞` manifold map between manifold-compatible diffeologies as a bundled
diffeologically smooth map. -/
def toDSmoothMap (f : C^∞⟮I, M; J, N⟯) : TauCeti.Diffeology.DSmoothMap M N :=
  ⟨f, f.contMDiff.dSmooth⟩

@[simp, grind =]
theorem coe_toDSmoothMap (f : C^∞⟮I, M; J, N⟯) : ⇑f.toDSmoothMap = ⇑f :=
  (rfl)

@[simp, grind =]
theorem toDSmoothMap_apply (f : C^∞⟮I, M; J, N⟯) (x : M) : f.toDSmoothMap x = f x :=
  (rfl)

theorem toDSmoothMap_injective :
    Injective (toDSmoothMap : C^∞⟮I, M; J, N⟯ → TauCeti.Diffeology.DSmoothMap M N) :=
  fun _ _ h ↦ ext fun x ↦ congr($(h) x)

@[simp]
theorem toDSmoothMap_id :
    (ContMDiffMap.id : C^∞⟮I, M; I, M⟯).toDSmoothMap = TauCeti.Diffeology.DSmoothMap.id M :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp; rfl

@[simp]
theorem toDSmoothMap_comp (g : C^∞⟮J, N; K, P⟯) (f : C^∞⟮I, M; J, N⟯) :
    (g.comp f).toDSmoothMap = g.toDSmoothMap.comp f.toDSmoothMap :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp

@[simp]
theorem toDSmoothMap_const (y : N) :
    (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯).toDSmoothMap =
      TauCeti.Diffeology.DSmoothMap.const M y :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp; rfl

@[simp]
theorem toDSmoothMap_fst :
    (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯).toDSmoothMap =
      TauCeti.Diffeology.DSmoothMap.fst :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp; rfl

@[simp]
theorem toDSmoothMap_snd :
    (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯).toDSmoothMap =
      TauCeti.Diffeology.DSmoothMap.snd :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp; rfl

@[simp]
theorem toDSmoothMap_prodMk (f : C^∞⟮K, P; I, M⟯) (g : C^∞⟮K, P; J, N⟯) :
    (f.prodMk g).toDSmoothMap = f.toDSmoothMap.prodMk g.toDSmoothMap :=
  TauCeti.Diffeology.DSmoothMap.ext fun _ ↦ by simp; rfl

end ContMDiffMap

namespace Diffeomorph

/-- View a `C^∞` manifold diffeomorphism between manifold-compatible diffeologies as a
diffeological diffeomorphism. -/
def toDSmoothEquiv (e : M ≃ₘ^∞⟮I, J⟯ N) : TauCeti.Diffeology.DSmoothEquiv M N :=
  .mk e.toEquiv e.contMDiff.dSmooth e.symm.contMDiff.dSmooth

@[simp, grind =]
theorem coe_toDSmoothEquiv (e : M ≃ₘ^∞⟮I, J⟯ N) : ⇑e.toDSmoothEquiv = ⇑e :=
  (rfl)

@[simp, grind =]
theorem toDSmoothEquiv_apply (e : M ≃ₘ^∞⟮I, J⟯ N) (x : M) : e.toDSmoothEquiv x = e x :=
  (rfl)

theorem toDSmoothEquiv_injective :
    Injective (toDSmoothEquiv : (M ≃ₘ^∞⟮I, J⟯ N) → TauCeti.Diffeology.DSmoothEquiv M N) :=
  fun _ _ h ↦ ext fun x ↦ congr($(h) x)

@[simp]
theorem toDSmoothEquiv_refl :
    (Diffeomorph.refl I M ∞).toDSmoothEquiv = TauCeti.Diffeology.DSmoothEquiv.refl M :=
  TauCeti.Diffeology.DSmoothEquiv.ext fun _ ↦ by simp

@[simp]
theorem toDSmoothEquiv_symm (e : M ≃ₘ^∞⟮I, J⟯ N) :
    e.symm.toDSmoothEquiv = e.toDSmoothEquiv.symm :=
  TauCeti.Diffeology.DSmoothEquiv.ext fun _ ↦ e.toDSmoothEquiv.eq_symm_apply.mpr (by simp)

@[simp]
theorem toDSmoothEquiv_trans (e₁ : M ≃ₘ^∞⟮I, J⟯ N) (e₂ : N ≃ₘ^∞⟮J, K⟯ P) :
    (e₁.trans e₂).toDSmoothEquiv = e₁.toDSmoothEquiv.trans e₂.toDSmoothEquiv :=
  TauCeti.Diffeology.DSmoothEquiv.ext fun _ ↦ by simp

end Diffeomorph

end ContMDiffMapBridge

namespace TauCeti.Diffeology

section ManifoldSource

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  [DiffeologicalSpace M] [IsContMDiffCompatible I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [DiffeologicalSpace N] [IsContMDiffCompatible J N]

namespace DSmoothMap

/-- Convert a bundled diffeologically smooth map out of a finite-dimensional boundaryless smooth
manifold into a bundled `C^∞` manifold map. -/
def toContMDiffMap (f : DSmoothMap M N) : C^∞⟮I, M; J, N⟯ :=
  ⟨f, f.dSmooth.contMDiff⟩

@[simp, grind =]
theorem coe_toContMDiffMap (f : DSmoothMap M N) :
    ⇑(f.toContMDiffMap : C^∞⟮I, M; J, N⟯) = ⇑f :=
  (rfl)

@[simp, grind =]
theorem toContMDiffMap_apply (f : DSmoothMap M N) (x : M) :
    (f.toContMDiffMap : C^∞⟮I, M; J, N⟯) x = f x :=
  (rfl)

@[simp]
theorem toDSmoothMap_toContMDiffMap (f : DSmoothMap M N) :
    (f.toContMDiffMap : C^∞⟮I, M; J, N⟯).toDSmoothMap = f :=
  ext fun _ ↦ rfl

@[simp]
theorem toContMDiffMap_toDSmoothMap (f : C^∞⟮I, M; J, N⟯) :
    f.toDSmoothMap.toContMDiffMap = f :=
  ContMDiffMap.ext fun _ ↦ rfl

/-- Equivalence identifying bundled diffeologically smooth maps `DSmoothMap M N` with
`C^∞⟮I, M; J, N⟯` when the source `M` is a finite-dimensional boundaryless smooth manifold. -/
def equivContMDiffMap : DSmoothMap M N ≃ C^∞⟮I, M; J, N⟯ where
  toFun := toContMDiffMap
  invFun := ContMDiffMap.toDSmoothMap
  left_inv := toDSmoothMap_toContMDiffMap
  right_inv := toContMDiffMap_toDSmoothMap

@[simp, grind =]
theorem equivContMDiffMap_apply (f : DSmoothMap M N) :
    equivContMDiffMap (I := I) (J := J) f = f.toContMDiffMap :=
  (rfl)

@[simp, grind =]
theorem equivContMDiffMap_symm_apply (f : C^∞⟮I, M; J, N⟯) :
    (equivContMDiffMap (I := I) (J := J)).symm f = f.toDSmoothMap :=
  (rfl)

end DSmoothMap

namespace DSmoothEquiv

variable [FiniteDimensional ℝ F] [IsManifold J ∞ N] [BoundarylessManifold J N]

/-- Convert a diffeological diffeomorphism between finite-dimensional boundaryless smooth manifolds
into a `C^∞` manifold diffeomorphism. -/
def toDiffeomorph (e : DSmoothEquiv M N) : M ≃ₘ^∞⟮I, J⟯ N where
  toEquiv := e.toEquiv
  contMDiff_toFun := e.dSmooth_toFun.contMDiff
  contMDiff_invFun := e.dSmooth_invFun.contMDiff

@[simp, grind =]
theorem coe_toDiffeomorph (e : DSmoothEquiv M N) :
    ⇑(e.toDiffeomorph : M ≃ₘ^∞⟮I, J⟯ N) = ⇑e :=
  (rfl)

@[simp, grind =]
theorem toDiffeomorph_apply (e : DSmoothEquiv M N) (x : M) :
    (e.toDiffeomorph : M ≃ₘ^∞⟮I, J⟯ N) x = e x :=
  (rfl)

@[simp]
theorem toDiffeomorph_symm (e : DSmoothEquiv M N) :
    (e.symm.toDiffeomorph : N ≃ₘ^∞⟮J, I⟯ M) = (e.toDiffeomorph : M ≃ₘ^∞⟮I, J⟯ N).symm :=
  Diffeomorph.ext fun _ ↦ EquivLike.injective (e.toDiffeomorph : M ≃ₘ^∞⟮I, J⟯ N) (by simp)

@[simp]
theorem toDSmoothEquiv_toDiffeomorph (e : DSmoothEquiv M N) :
    (e.toDiffeomorph : M ≃ₘ^∞⟮I, J⟯ N).toDSmoothEquiv = e :=
  ext fun _ ↦ rfl

@[simp]
theorem toDiffeomorph_toDSmoothEquiv (e : M ≃ₘ^∞⟮I, J⟯ N) :
    e.toDSmoothEquiv.toDiffeomorph = e :=
  Diffeomorph.ext fun _ ↦ rfl

/-- Equivalence identifying diffeological diffeomorphisms `DSmoothEquiv M N` with `C^∞` manifold
diffeomorphisms `M ≃ₘ^∞⟮I, J⟯ N` between finite-dimensional boundaryless smooth manifolds. -/
def equivDiffeomorph : DSmoothEquiv M N ≃ (M ≃ₘ^∞⟮I, J⟯ N) where
  toFun := toDiffeomorph
  invFun := Diffeomorph.toDSmoothEquiv
  left_inv := toDSmoothEquiv_toDiffeomorph
  right_inv := toDiffeomorph_toDSmoothEquiv

@[simp, grind =]
theorem equivDiffeomorph_apply (e : DSmoothEquiv M N) :
    equivDiffeomorph (I := I) (J := J) e = e.toDiffeomorph :=
  (rfl)

@[simp, grind =]
theorem equivDiffeomorph_symm_apply (e : M ≃ₘ^∞⟮I, J⟯ N) :
    (equivDiffeomorph (I := I) (J := J)).symm e = e.toDSmoothEquiv :=
  (rfl)

end DSmoothEquiv

end ManifoldSource

end TauCeti.Diffeology

namespace TauCeti

section SmoothMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  [DiffeologicalSpace G] [IsContMDiffCompatible I G]

/-- Multiplication on a manifold-compatible space with smooth multiplication is diffeologically
smooth. -/
@[to_additive
/-- Addition on a manifold-compatible space with smooth addition is diffeologically smooth. -/]
theorem dSmooth_mul [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun p : G × G ↦ p.1 * p.2) :=
  (contMDiff_mul I ∞).dSmooth

/-- Inversion on a manifold-compatible Lie group is diffeologically smooth. -/
@[to_additive
/-- Negation on a manifold-compatible additive Lie group is diffeologically smooth. -/]
theorem dSmooth_inv [Group G] [LieGroup I ∞ G] :
    DSmooth (Inv.inv : G → G) :=
  (contMDiff_inv I ∞).dSmooth

/-- Left translation `g ↦ (smoothLeftMul I g).toDSmoothMap` on a manifold-compatible space with
smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_smoothLeftMul_toDSmoothMap [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun g : G ↦ (smoothLeftMul I g).toDSmoothMap) :=
  Diffeology.DSmoothMap.dSmooth_iff_uncurry.mpr (dSmooth_mul I)

/-- Right translation `g ↦ (smoothRightMul I g).toDSmoothMap` on a manifold-compatible space with
smooth multiplication is smooth into the functional diffeology `DSmoothMap G G`. -/
@[fun_prop]
theorem dSmooth_smoothRightMul_toDSmoothMap [Mul G] [ContMDiffMul I ∞ G] :
    DSmooth (fun g : G ↦ (smoothRightMul I g).toDSmoothMap) :=
  Diffeology.DSmoothMap.dSmooth_iff_uncurry.mpr ((dSmooth_mul I).comp Diffeology.dSmooth_swap)

end SmoothMul

end TauCeti

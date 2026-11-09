/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The cotangent relation of a map

A differentiable map `f : M → N` pulls a covector at `f x` back to a covector at `x`.
It need not induce a map from `T*M` to `T*N`: the transpose of its differential need
not be invertible. `TauCeti.CotangentBundle.cotangentRel I J f` records instead the
relation between `(x, p)` and `(f x, q)` given by `p = q ∘ df_x`.

The relation of the identity is equality, and the relation of a composite is exactly
the composite of the relations. For diffeomorphisms it is the graph of the existing
cotangent lift `Diffeomorph.cotangent`. Under `TauCeti.CotangentBundle.prodDiffeomorph`,
the cotangent relation of a product map `Prod.map i₁ i₂` splits into the cotangent
relations of its factors (`TauCeti.CotangentBundle.cotangentRel_prodMap_iff`). For
constant maps, all target covectors over the constant value are related to the zero
source covector; this illustrates why a relation is necessary for general maps.

The definition uses Mathlib's `mfderiv`, with its usual zero value at points where
the map is not differentiable. The composition and product theorems assume
differentiability only at the source point (and its image, for composition). No
finite-dimensionality or boundaryless assumptions are needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Chapter 11 (pullback of covectors).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 F H')
  {H'' : Type*} [TopologicalSpace H''] (K : ModelWithCorners 𝕜 G H'')
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- The cotangent relation of `f` relates a source covector `p` to a target covector `q`
when their base points lie over `f` and `p` is the pullback of `q` by the differential.
At nondifferentiable points this uses the usual zero convention for `mfderiv`. -/
def cotangentRel (f : M → N) (z : CotangentBundle I M) (w : CotangentBundle J N) : Prop :=
  f z.proj = w.proj ∧ z.2 = w.2 ∘L mfderiv I J f z.proj

/-- A pair belongs to the cotangent relation precisely when it lies over the map and
the source covector is the pullback of the target covector. -/
theorem cotangentRel_iff (f : M → N) (z : CotangentBundle I M) (w : CotangentBundle J N) :
    cotangentRel I J f z w ↔
      f z.proj = w.proj ∧ z.2 = w.2 ∘L mfderiv I J f z.proj :=
  Iff.rfl

/-- For covectors with the prescribed base points, membership is equality with the
linear pullback. -/
@[simp]
theorem cotangentRel_mk_iff (f : M → N) (x : M)
    (p : TangentSpace I x →L[𝕜] 𝕜) (q : TangentSpace J (f x) →L[𝕜] 𝕜) :
    cotangentRel I J f (TotalSpace.mk' (E →L[𝕜] 𝕜) x p)
      (TotalSpace.mk' (F →L[𝕜] 𝕜) (f x) q) ↔ p = q ∘L mfderiv I J f x := by
  simp [cotangentRel_iff]

variable {I J K}

/-- Related cotangent vectors lie over the graph of the base map. -/
theorem cotangentRel_proj {f : M → N} {z : CotangentBundle I M} {w : CotangentBundle J N}
    (h : cotangentRel I J f z w) : f z.proj = w.proj :=
  h.1

/-- Related covectors have the same pairing with a tangent vector and its image. -/
theorem cotangentRel_snd_apply {f : M → N} {z : CotangentBundle I M}
    {w : CotangentBundle J N} (h : cotangentRel I J f z w) (v : TangentSpace I z.proj) :
    z.2 v = w.2 (mfderiv I J f z.proj v) :=
  DFunLike.congr_fun h.2 v

variable (I)

/-- The cotangent relation of the identity map is the diagonal. -/
@[simp]
theorem cotangentRel_id_iff (z w : CotangentBundle I M) :
    cotangentRel I I id z w ↔ z = w := by
  constructor
  · intro h
    apply CotangentBundle.ext h.1
    intro v
    simpa using cotangentRel_snd_apply h v
  · rintro rfl
    simp [cotangentRel_iff, mfderiv_id]

variable (J K)

/-- The cotangent relation of a composite equals relational composition. In particular,
every related pair factors through a covector at the intermediate base point. -/
theorem cotangentRel_comp_iff {f : M → N} {g : N → P}
    (z : CotangentBundle I M) (u : CotangentBundle K P)
    (hf : MDifferentiableAt I J f z.proj) (hg : MDifferentiableAt J K g (f z.proj)) :
    cotangentRel I K (g ∘ f) z u ↔
      Relation.Comp (cotangentRel I J f) (cotangentRel J K g) z u := by
  constructor
  · intro h
    refine ⟨TotalSpace.mk' (F →L[𝕜] 𝕜) (f z.proj)
      (u.2 ∘L mfderiv J K g (f z.proj)), ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      ext v
      exact (cotangentRel_snd_apply h v).trans
        (congrArg u.2 (mfderiv_comp_apply _ hg hf v))
    · exact ⟨h.1, rfl⟩
  · rintro ⟨w, hzw, hwu⟩
    refine ⟨(congrArg g hzw.1).trans hwu.1, ?_⟩
    ext v
    calc
      z.2 v = w.2 (mfderiv I J f z.proj v) := cotangentRel_snd_apply hzw v
      _ = u.2 (mfderiv J K g w.proj (mfderiv I J f z.proj v)) :=
        cotangentRel_snd_apply hwu _
      _ = u.2 (mfderiv I K (g ∘ f) z.proj v) := by
        rw [← hzw.1]
        exact congrArg u.2 (mfderiv_comp_apply _ hg hf v).symm

/-- The zero sections of the source and target are related over every base point. -/
@[simp]
theorem cotangentRel_zeroSection (f : M → N) (x : M) :
    cotangentRel I J f (zeroSection (E →L[𝕜] 𝕜) _ x)
      (zeroSection (F →L[𝕜] 𝕜) _ (f x)) := by
  refine ⟨(zeroSection_proj ..).symm, ?_⟩
  simp only [zeroSection_snd]
  exact (ContinuousLinearMap.zero_comp _).symm

/-- A constant map relates exactly zero source covectors to arbitrary target covectors
over its value. -/
@[simp]
theorem cotangentRel_const_iff (y : N) (z : CotangentBundle I M) (w : CotangentBundle J N) :
    cotangentRel I J (fun _ : M ↦ y) z w ↔ y = w.proj ∧ z.2 = 0 := by
  -- `ContinuousLinearMap.comp_zero` does not apply directly: the zero differential has
  -- codomain `TangentSpace J y`, while `w.2` is a covector at `w.proj`.
  have h0 : w.2 ∘L mfderiv I J (fun _ : M ↦ y) z.proj = 0 := by
    ext v
    change w.2 (mfderiv I J (fun _ : M ↦ y) z.proj v) = 0
    rw [mfderiv_const]
    exact w.2.map_zero
  rw [cotangentRel_iff, h0]

section Diffeomorph

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- For a diffeomorphism, the cotangent relation is the graph of its cotangent lift. -/
@[simp]
theorem cotangentRel_diffeomorph_iff (h : M ≃ₘ⟮I, J⟯ N)
    (z : CotangentBundle I M) (w : CotangentBundle J N) :
    cotangentRel I J h z w ↔ h.cotangent z = w := by
  constructor
  · intro hz
    apply CotangentBundle.ext ((Diffeomorph.proj_cotangent h z).trans hz.1)
    intro v
    exact (h.cotangent_snd_apply z v).trans ((cotangentRel_snd_apply hz _).trans
      (congrArg w.2 (h.mfderiv_apply_mfderiv_symm_apply (by simp) z.proj v)))
  · rintro rfl
    refine ⟨(Diffeomorph.proj_cotangent h z).symm, ?_⟩
    ext v
    exact (Diffeomorph.cotangent_snd_apply_mfderiv h z v).symm

end Diffeomorph

section ProductMap

variable {E₁ E₂ F₁ F₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {H₁ H₂ G₁ G₂ : Type*}
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₁ : ModelWithCorners 𝕜 F₁ G₁} {J₂ : ModelWithCorners 𝕜 F₂ G₂}
  {M₁ M₂ Q₁ Q₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace Q₁] [ChartedSpace G₁ Q₁]
  [TopologicalSpace Q₂] [ChartedSpace G₂ Q₂]
  [IsManifold I₁ 2 M₁] [IsManifold I₂ 2 M₂]
  [IsManifold J₁ 2 Q₁] [IsManifold J₂ 2 Q₂]

/-- **The cotangent relation of a product map splits under `prodDiffeomorph`.** Assuming `i₁` and
`i₂` are differentiable at the two components of `z.proj`, `Prod.map i₁ i₂` relates `z` to `w` if
and only if `i₁` and `i₂` relate the corresponding factors of `prodDiffeomorph z` and
`prodDiffeomorph w`. -/
theorem cotangentRel_prodMap_iff {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (z : CotangentBundle (J₁.prod J₂) (Q₁ × Q₂))
    (w : CotangentBundle (I₁.prod I₂) (M₁ × M₂))
    (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.proj.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.proj.2) :
    cotangentRel (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z w ↔
      cotangentRel J₁ I₁ i₁ (prodDiffeomorph J₁ J₂ Q₁ Q₂ z).1
        (prodDiffeomorph I₁ I₂ M₁ M₂ w).1 ∧
      cotangentRel J₂ I₂ i₂ (prodDiffeomorph J₁ J₂ Q₁ Q₂ z).2
        (prodDiffeomorph I₁ I₂ M₁ M₂ w).2 := by
  obtain ⟨⟨q₁, q₂⟩, α⟩ := z
  obtain ⟨⟨x₁, x₂⟩, β⟩ := w
  have hdiff : MDifferentiableAt (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) :=
    (hi₁.comp (q₁, q₂) mdifferentiableAt_fst).prodMk (hi₂.comp (q₁, q₂) mdifferentiableAt_snd)
  rw [prodDiffeomorph_fst, prodDiffeomorph_fst, prodDiffeomorph_snd, prodDiffeomorph_snd]
  simp only [cotangentRel_iff]
  constructor
  · rintro ⟨hproj, hrel⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hproj
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩
    · rw [hrel, ContinuousLinearMap.comp_assoc, mfderiv_prodMap_comp_prodMkLeft hi₂,
        ← ContinuousLinearMap.comp_assoc]
    · rw [hrel, ContinuousLinearMap.comp_assoc, mfderiv_prodMap_comp_prodMkRight hi₁,
        ← ContinuousLinearMap.comp_assoc]
  · rintro ⟨⟨rfl, hrel₁⟩, ⟨rfl, hrel₂⟩⟩
    refine ⟨rfl, ContinuousLinearMap.ext fun v ↦ ?_⟩
    rw [ContinuousLinearMap.comp_apply]
    have hz := snd_apply_eq_prodDiffeomorph_add (I := J₁) (J := J₂) ⟨(q₁, q₂), α⟩ v
    have hw := snd_apply_eq_prodDiffeomorph_add (I := I₁) (J := I₂) ⟨(i₁ q₁, i₂ q₂), β⟩
      (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v)
    rw [prodDiffeomorph_fst, prodDiffeomorph_snd] at hz hw
    dsimp only at hz hw
    rw [hz, hw]
    have h₁ : mfderiv (I₁.prod I₂) I₁ Prod.fst (i₁ q₁, i₂ q₂)
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v) =
        mfderiv J₁ I₁ i₁ q₁ (mfderiv (J₁.prod J₂) J₁ Prod.fst (q₁, q₂) v) :=
      (mfderiv_comp_apply (q₁, q₂) (mdifferentiableAt_fst (x := (i₁ q₁, i₂ q₂))) hdiff v).symm
        |>.trans (mfderiv_comp_apply (q₁, q₂) hi₁ mdifferentiableAt_fst v)
    have h₂ : mfderiv (I₁.prod I₂) I₂ Prod.snd (i₁ q₁, i₂ q₂)
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v) =
        mfderiv J₂ I₂ i₂ q₂ (mfderiv (J₁.prod J₂) J₂ Prod.snd (q₁, q₂) v) :=
      (mfderiv_comp_apply (q₁, q₂) (mdifferentiableAt_snd (x := (i₁ q₁, i₂ q₂))) hdiff v).symm
        |>.trans (mfderiv_comp_apply (q₁, q₂) hi₂ mdifferentiableAt_snd v)
    rw [h₁, h₂]
    exact congrArg₂ (· + ·) (DFunLike.congr_fun hrel₁ _) (DFunLike.congr_fun hrel₂ _)

end ProductMap

end TauCeti.CotangentBundle

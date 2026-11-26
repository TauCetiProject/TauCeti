/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Symplectic.Manifold.PrescribedDerivative

/-!
# The symplectic neighbourhood theorem

Let `i : Q → M` and `j : Q' → N` be embeddings of symplectic submanifolds, for nondegenerate
two-forms `θ` on `M` and `σ` on `N`
(`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages`).
Along each of them the ambient tangent space splits as the tangent space of the submanifold plus
its symplectic complement, and the normal space carries the normal symplectic form
(`TauCeti.SmoothEmbedding.symplecticNormalForm`) under which normal classes pair as their
symplectic representatives (`TauCeti.SmoothEmbedding.symplecticNormalRepresentative`).

Given a map `f : Q → Q'` and linear maps `C q : ν_i(q) → ν_j(f q)` of normal spaces, the **ambient
extension** `TauCeti.SmoothEmbedding.symplecticNormalExtension` is the linear map
`T_(i q) M → T_(j (f q)) N` sending `di_q u` to `dj (df_q u)` and the symplectic representative of
`ν` to the symplectic representative of `C q ν`; these two conditions determine it
(`TauCeti.SmoothEmbedding.eq_symplecticNormalExtension`). It induces `C q` on normal spaces
(`TauCeti.SmoothEmbedding.normalClass_symplecticNormalExtension`). If `f` carries the form induced
by `σ` to the form induced by `θ` and `C q` is symplectic for the normal symplectic forms, then
the ambient extension carries `σ` to `θ` on the full ambient tangent space
(`TauCeti.SmoothEmbedding.eval₂_symplecticNormalExtension`), because the two summands are
`σ`-orthogonal. It is invertible when `df_q` and `C q` are
(`TauCeti.SmoothEmbedding.isInvertible_symplecticNormalExtension`), and smooth for smooth `f`
when the symplectic representatives `v ↦ r_j (C q [v])` depend smoothly on ambient tangent
vectors along `i` (`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalExtension`): its tangential
part is `df_q` applied to `(i^* θ)⁻¹ (θ(v, di_q ·))`, built from the inverse of the flat map of
the induced form. This holds for a smooth normal-bundle map `C`
(`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalRepresentative_comp_normalClass`).

These are exactly the data of the neighbourhood theorem with a prescribed ambient derivative. The
tubular construction `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq` realizes the
ambient extension as the differential along `i(Q)` of a partial diffeomorphism, which therefore
pulls `σ` back to a form agreeing with `θ` on every ambient tangent space along `i(Q)`, and relative
Moser (`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq`) corrects it to a
symplectomorphism of neighbourhoods with the same differential. This proves the **symplectic
neighbourhood theorem**
(`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq_symplecticNormalExtension`): for
closed nondegenerate `θ` and `σ` on Hausdorff, second-countable manifolds without boundary, and
compact nonempty `Q`, a symplectomorphism of the submanifolds together with a smooth symplectic
isomorphism of their normal bundles over it extends to a symplectomorphism `φ` of open
neighbourhoods, with `φ ∘ i = j ∘ f` and differential the ambient extension along `i(Q)`. In other
words, two compact nonempty symplectic submanifolds that are symplectomorphic by `f`, and whose
symplectic normal bundles are isomorphic over `f`, have symplectomorphic neighbourhoods.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Theorem 3.4.10.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorems 7.4 and 8.4.
-/

public section

noncomputable section

open Bundle Manifold Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti


namespace SmoothEmbedding

open SmoothTwoForm

variable {E E' V F H H' G G' Q Q' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ V G} {K : ModelWithCorners ℝ F G'}
  [TopologicalSpace Q] [ChartedSpace H Q] [TopologicalSpace Q'] [ChartedSpace H' Q']
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace G' N] [IsManifold K ∞ N]
  {n n' : ℕ∞ω} {θ : SmoothTwoForm J M} {hθ : θ.IsNondegenerate}
  {σ : SmoothTwoForm K N} {hσ : σ.IsNondegenerate}

/-- The tangential part of an ambient tangent vector `v` along a symplectic submanifold: the
tangent vector `u` of `Q` with `di_q u = v - r`, where `r` is the symplectic representative of
the normal class of `v`. -/
private def tangentialPart (θ : SmoothTwoForm J M) (i : SmoothEmbedding I J n Q M) (q : Q) :
    TangentSpace J (i q) →L[ℝ] TangentSpace I q :=
  ((i.tangentPairing θ q).comp (mfderiv I J i q)).inverse.comp (i.tangentPairing θ q)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The tangential part of `v` inverts the induced form on the pairings `θ(v, di_q ·)`. -/
private theorem tangentialPart_apply (θ : SmoothTwoForm J M) (i : SmoothEmbedding I J n Q M)
    (q : Q) (v : TangentSpace J (i q)) :
    tangentialPart θ i q v = ((i.tangentPairing θ q).comp (mfderiv I J i q)).inverse
      ((flat θ (i q) v).comp (mfderiv I J i q)) := by
  rw [tangentialPart, ContinuousLinearMap.comp_apply, tangentPairing_apply]

private theorem mfderiv_tangentialPart (i : SmoothEmbedding I J n Q M)
    (hi : hθ.HasSymplecticTangentImages I i) (q : Q) (hn : n ≠ 0) (v : TangentSpace J (i q)) :
    mfderiv I J i q (tangentialPart θ i q v) =
      v - i.symplecticNormalRepresentative hi q hn (i.isImmersion.normalClass q hn v) := by
  rw [i.symplecticNormalRepresentative_normalClass_eq_sub_mfderiv_inverse hi q hn _
    (i.tangentPairing_comp_apply θ q) v, sub_sub_cancel, tangentialPart_apply]

private theorem tangentialPart_mfderiv (i : SmoothEmbedding I J n Q M)
    (hi : hθ.HasSymplecticTangentImages I i) (q : Q) (hn : n ≠ 0) (u : TangentSpace I q) :
    tangentialPart θ i q (mfderiv I J i q u) = u := by
  apply i.isImmersion.mfderiv_injective hn q
  rw
      [mfderiv_tangentialPart i hi q hn, Manifold.IsImmersion.normalClass_mfderiv, map_zero,
          sub_zero]

/-- **The ambient extension of tangent and symplectic normal data.** Along symplectic submanifold
embeddings `i : Q → M` and `j : Q' → N`, a map `f : Q → Q'` and linear maps
`C q : ν_i(q) → ν_j(f q)` of normal spaces determine the linear map
`T_(i q) M → T_(j (f q)) N` which sends `di_q u` to `dj (df_q u)` and the symplectic
representative of a normal class `ν` to the symplectic representative of `C q ν`. The ambient
tangent space is the direct sum of the tangent space of the submanifold and its symplectic
complement, so these two requirements determine it. -/
def symplecticNormalExtension (θ : SmoothTwoForm J M) (i : SmoothEmbedding I J n Q M)
    (j : SmoothEmbedding I' K n' Q' N)
    (hj : hσ.HasSymplecticTangentImages I' j) (f : Q → Q') (hn : n ≠ 0) (hn' : n' ≠ 0)
    (C : ∀ q, i.isImmersion.NormalSpace q hn →L[ℝ] j.isImmersion.NormalSpace (f q) hn') (q : Q) :
    TangentSpace J (i q) →L[ℝ] TangentSpace K (j (f q)) :=
  (mfderiv I' K j (f q)).comp ((mfderiv I I' f q).comp (tangentialPart θ i q)) +
    (j.symplecticNormalRepresentative hj (f q) hn').comp
        ((C q).comp (i.isImmersion.normalClassL q hn))


section Extension

variable (i : SmoothEmbedding I J n Q M) (hi : hθ.HasSymplecticTangentImages I i)
  (j : SmoothEmbedding I' K n' Q' N) (hj : hσ.HasSymplecticTangentImages I' j) (f : Q → Q')
  (hn : n ≠ 0) (hn' : n' ≠ 0)
      (C : ∀ q, i.isImmersion.NormalSpace q hn →L[ℝ] j.isImmersion.NormalSpace (f q) hn')

/-- An ambient tangent vector is the sum of its tangential part and the symplectic representative
of its normal class. -/
private theorem mfderiv_tangentialPart_add (q : Q) (v : TangentSpace J (i q)) :
    mfderiv I J i q (tangentialPart θ i q v) +
      i.symplecticNormalRepresentative hi q hn (i.isImmersion.normalClass q hn v) = v := by
  rw [mfderiv_tangentialPart i hi q hn, sub_add_cancel]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
private theorem symplecticNormalExtension_apply (q : Q) (v : TangentSpace J (i q)) :
    symplecticNormalExtension θ i j hj f hn hn' C q v =
      mfderiv I' K j (f q) (mfderiv I I' f q (tangentialPart θ i q v)) +
        j.symplecticNormalRepresentative hj (f q) hn' (C q (i.isImmersion.normalClass q hn v)) := by
  simp [symplecticNormalExtension, Manifold.IsImmersion.normalClassL_apply]

include hi in
/-- The ambient extension sends the tangent vector `di_q u` of the submanifold to `dj (df_q u)`. -/
@[simp]
theorem symplecticNormalExtension_mfderiv (q : Q) (u : TangentSpace I q) :
    symplecticNormalExtension θ i j hj f hn hn' C q (mfderiv I J i q u) =
      mfderiv I' K j (f q) (mfderiv I I' f q u) := by
  rw
      [symplecticNormalExtension_apply, tangentialPart_mfderiv i hi q hn,
          Manifold.IsImmersion.normalClass_mfderiv,
    map_zero, map_zero, add_zero]

/-- The ambient extension sends the symplectic representative of a normal class `ν` to the
symplectic representative of `C q ν`. -/
@[simp]
theorem symplecticNormalExtension_symplecticNormalRepresentative (q : Q)
    (ν : i.isImmersion.NormalSpace q hn) :
    symplecticNormalExtension θ i j hj f hn hn' C q (i.symplecticNormalRepresentative hi q hn ν) =
      j.symplecticNormalRepresentative hj (f q) hn' (C q ν) := by
  have h0 : tangentialPart θ i q (i.symplecticNormalRepresentative hi q hn ν) = 0 := by
    apply i.isImmersion.mfderiv_injective hn q
    rw [mfderiv_tangentialPart i hi q hn, normalClass_symplecticNormalRepresentative, sub_self,
      map_zero]
  rw [symplecticNormalExtension_apply, h0, normalClass_symplecticNormalRepresentative, map_zero,
    map_zero, zero_add]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The ambient extension induces `C q` on normal spaces. -/
@[simp]
theorem normalClass_symplecticNormalExtension (q : Q) (v : TangentSpace J (i q)) :
    j.isImmersion.normalClass (f q) hn' (symplecticNormalExtension θ i j hj f hn hn' C q v) =
      C q (i.isImmersion.normalClass q hn v) := by
  rw [symplecticNormalExtension_apply, map_add, Manifold.IsImmersion.normalClass_mfderiv, zero_add,
    normalClass_symplecticNormalRepresentative]

/-- **Uniqueness of the ambient extension.** A linear map which sends `di_q u` to `dj (df_q u)`
and symplectic representatives of normal classes `ν` to symplectic representatives of `C q ν` is
the ambient extension. -/
theorem eq_symplecticNormalExtension (q : Q)
    (L : TangentSpace J (i q) →L[ℝ] TangentSpace K (j (f q)))
    (hL : ∀ u, L (mfderiv I J i q u) = mfderiv I' K j (f q) (mfderiv I I' f q u))
    (hLν : ∀ ν, L (i.symplecticNormalRepresentative hi q hn ν) =
      j.symplecticNormalRepresentative hj (f q) hn' (C q ν)) :
    L = symplecticNormalExtension θ i j hj f hn hn' C q := by
  ext v
  rw [← mfderiv_tangentialPart_add i hi hn q v, map_add, map_add, hL, hLν,
    symplecticNormalExtension_mfderiv i hi j hj f hn hn' C,
    symplecticNormalExtension_symplecticNormalRepresentative i hi j hj f hn hn' C]


include hi in
/-- **The ambient extension is symplectic.** If `f` carries the form induced by `σ` on `Q'` to
the form induced by `θ` on `Q` at `q`, and `C q` carries the normal symplectic form of `j` to that
of `i`, then the ambient extension carries `σ` to `θ` on the full ambient tangent space. -/
theorem eval₂_symplecticNormalExtension (q : Q)
    (hf : ∀ u w, SmoothBundleForm.eval₂ σ (j (f q)) (mfderiv I' K j (f q) (mfderiv I I' f q u))
        (mfderiv I' K j (f q) (mfderiv I I' f q w)) =
      SmoothBundleForm.eval₂ θ (i q) (mfderiv I J i q u) (mfderiv I J i q w))
    (hC : ∀ ν ν', j.symplecticNormalForm hj (f q) hn' (C q ν) (C q ν') =
      i.symplecticNormalForm hi q hn ν ν') (v w : TangentSpace J (i q)) :
    SmoothBundleForm.eval₂ σ (j (f q)) (symplecticNormalExtension θ i j hj f hn hn' C q v)
        (symplecticNormalExtension θ i j hj f hn hn' C q w) =
      SmoothBundleForm.eval₂ θ (i q) v w := by
  conv_rhs =>
    rw [← mfderiv_tangentialPart_add i hi hn q v, ← mfderiv_tangentialPart_add i hi hn q w]
  rw [symplecticNormalExtension_apply, symplecticNormalExtension_apply]
  simp only [SmoothBundleForm.eval₂_add_left, SmoothBundleForm.eval₂_add_right,
    eval₂_mfderiv_symplecticNormalRepresentative, eval₂_symplecticNormalRepresentative_mfderiv,
    add_zero, zero_add, hf, ← symplecticNormalForm_apply, hC]

include hi in
/-- The ambient extension is invertible when the differential of `f` at `q` and `C q` are. -/
theorem isInvertible_symplecticNormalExtension (q : Q) (hf : (mfderiv I I' f q).IsInvertible)
    (hC : (C q).IsInvertible) :
    (symplecticNormalExtension θ i j hj f hn hn' C q).IsInvertible := by
  set A := symplecticNormalExtension θ i j hj f hn hn' C q
  have hinj : Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv ↦ ?_
    -- The normal class of `v` is killed by `C q`, so `v = di_q u`; then `dj (df_q u) = 0`
    -- forces `u = 0`.
    have hν : i.isImmersion.normalClass q hn v = 0 := by
      apply hC.injective
      rw [← normalClass_symplecticNormalExtension i j hj f hn hn' C, hv, map_zero, map_zero]
    obtain ⟨u, rfl⟩ := (i.isImmersion.mem_tangentRange_iff q hn _).1
        ((i.isImmersion.normalClass_eq_zero_iff q hn _).1 hν)
    have h0 : mfderiv I' K j (f q) (mfderiv I I' f q u) = 0 := by
      rw [← symplecticNormalExtension_mfderiv i hi j hj f hn hn' C]
      exact hv
    rw [(injective_iff_map_eq_zero _).1 hf.injective u
      ((injective_iff_map_eq_zero _).1 (j.isImmersion.mfderiv_injective hn' (f q)) _ h0),
      map_zero]
  have hsurj : Surjective A := by
    intro w
    -- `w` is `dj b` plus the symplectic representative of its class; take
    -- `v = di (df⁻¹ b) + r_i (C⁻¹ [w])`.
    obtain ⟨b, hb⟩ := (j.isImmersion.mem_tangentRange_iff (f q) hn' _).1
      ((j.isImmersion.normalClass_eq_zero_iff (f q) hn' _).1 (by
        rw [map_sub, normalClass_symplecticNormalRepresentative, sub_self] :
          j.isImmersion.normalClass (f q) hn' (w - j.symplecticNormalRepresentative hj (f q) hn'
            (j.isImmersion.normalClass (f q) hn' w)) = 0))
    obtain ⟨u, rfl⟩ := hf.surjective b
    obtain ⟨ν, hν⟩ := hC.surjective (j.isImmersion.normalClass (f q) hn' w)
    refine ⟨mfderiv I J i q u + i.symplecticNormalRepresentative hi q hn ν, ?_⟩
    rw [map_add, symplecticNormalExtension_mfderiv i hi j hj f hn hn' C,
      symplecticNormalExtension_symplecticNormalRepresentative i hi j hj f hn hn' C, hb, hν,
      sub_add_cancel]
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  -- The tangent spaces are the model spaces, which carry the normed structure.
  exact (ContinuousLinearMap.isInvertible_iff_bijective (E := V) (F := F) (f := A)).2
    ⟨hinj, hsurj⟩


end Extension


section Smooth

variable [IsManifold I ∞ Q] [IsManifold I' ∞ Q']

omit [FiniteDimensional ℝ V] in
/-- **Smoothness of the ambient extension.** For smooth `f` and normal maps `C q` whose
symplectic representatives `v ↦ r_j (C q [v])` depend smoothly on the ambient tangent vector `v`
of `M` along `i`, the ambient extension is smooth on the pulled-back ambient tangent bundle. -/
theorem contMDiff_symplecticNormalExtension (i : SmoothEmbedding I J ∞ Q M)
    (hi : hθ.HasSymplecticTangentImages I i) (j : SmoothEmbedding I' K ∞ Q' N)
    (hj : hσ.HasSymplecticTangentImages I' j) {f : Q → Q'} (hf : ContMDiff I I' ∞ f)
    (hn : (∞ : ℕ∞ω) ≠ 0)
        (C : ∀ q, i.isImmersion.NormalSpace q hn →L[ℝ] j.isImmersion.NormalSpace (f q) hn)
    (hC : ContMDiff (I.prod 𝓘(ℝ, V)) (K.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨j (f p.proj), j.symplecticNormalRepresentative hj (f p.proj) hn
          (C p.proj (i.isImmersion.normalClass p.proj hn p.snd))⟩ : TangentBundle K N))) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (K.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨j (f p.proj), symplecticNormalExtension θ i j hj f hn hn C p.proj p.snd⟩ :
          TangentBundle K N)) := by
  -- The tangential part is smooth into `T Q`; push it forward by `df` and then `dj`.
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, tangentialPart θ i p.proj p.snd⟩ : TangentBundle I Q)) :=
    (i.contMDiff_inverse_comp_mfderiv (m := ∞) (by simp)
      (i.contMDiff_of_eval₂_mfderiv (by simp) (by simp) (i.tangentPairing_comp_apply θ))
      (fun q ↦ i.isInvertible_of_eval₂_mfderiv hi q hn _ (i.tangentPairing_comp_apply θ q))
      (contMDiff_flat θ)).congr fun p ↦
      congrArg (TotalSpace.mk p.proj) (tangentialPart_apply θ i p.proj p.snd)
  -- `tangentMap` is `⟨x, v⟩ ↦ ⟨f x, df_x v⟩` by definition.
  have ht : ContMDiff (I.prod 𝓘(ℝ, V)) (K.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' F (E := TangentSpace K) (j (f p.proj))
          (mfderiv I' K j (f p.proj) (mfderiv I I' f p.proj (tangentialPart θ i p.proj p.snd)))) :=
    (j.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
      ((hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hu)
  exact (ContMDiff.add_sectionAlong ht hC).congr fun p ↦ congrArg (TotalSpace.mk (j (f p.proj)))
    (symplecticNormalExtension_apply i j hj f hn hn C p.proj p.snd)


variable [FiniteDimensional ℝ E'] {P P' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']

/-- A smooth map `C` of normal bundles over `f` has symplectic representatives
`v ↦ r_j (C q [v])` depending smoothly on the ambient tangent vector `v` of `M` along `i`. -/
theorem contMDiff_symplecticNormalRepresentative_comp_normalClass (i : SmoothEmbedding I J ∞ Q M)
    (j : SmoothEmbedding I' K ∞ Q' N) (hj : hσ.HasSymplecticTangentImages I' j) {f : Q → Q'}
    (hn : (∞ : ℕ∞ω) ≠ 0)
        (C : ∀ q, i.isImmersion.NormalSpace q hn →L[ℝ] j.isImmersion.NormalSpace (f q) hn)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hdim' : Module.finrank ℝ P' = Module.finrank ℝ F - Module.finrank ℝ E')
    (hC : letI := i.normalSpaceFiberBundle hn hdim
      letI := j.normalSpaceFiberBundle hn hdim'
      ContMDiff (I.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, P')) ∞
        (fun p : TotalSpace P (fun q ↦ i.isImmersion.NormalSpace q hn) ↦
          (⟨f p.proj, C p.proj p.snd⟩ : TotalSpace P'
              (fun q' ↦ j.isImmersion.NormalSpace q' hn)))) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (K.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨j (f p.proj), j.symplecticNormalRepresentative hj (f p.proj) hn
          (C p.proj (i.isImmersion.normalClass p.proj hn p.snd))⟩ : TangentBundle K N)) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := j.normalSpaceFiberBundle hn hdim'
  exact (j.contMDiff_symplecticNormalRepresentative hj hn (m := ∞) (by simp) (by simp) hdim').comp
    (hC.comp (i.contMDiff_normalQuotientMap hn (m := ∞) (by simp) hdim)) |>.congr fun p ↦ by
      rw [comp_apply, comp_apply, normalQuotientMap_apply]

end Smooth


/-! ### The symplectic neighbourhood theorem -/

section Neighborhood

variable [FiniteDimensional ℝ E'] [IsManifold I ∞ Q] [IsManifold I' ∞ Q']
  {P P' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']

/-- **The symplectic neighbourhood theorem.** Let `i : Q → M` and `j : Q' → N` be embeddings of
symplectic submanifolds of manifolds with symplectic forms `θ` and `σ`, with `Q` compact, let
`f : Q → Q'` be a diffeomorphism carrying the form induced by `σ` to the form induced by `θ`, and
let `C q : ν_i(q) → ν_j(f q)` be a smooth isomorphism of normal bundles over `f` carrying the
normal symplectic form of `j` to that of `i`. Then there are open neighbourhoods `U₀` of `i(Q)`
and `U₁` of `j(Q')` and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ`, with
`φ (i q) = j (f q)`, whose differential at `i q` is the ambient extension of `df_q` and `C q`:
it sends `di_q u` to `dj (df_q u)` and induces `C q` on normal spaces. -/
theorem exists_diffeomorph_opens_mfderiv_eq_symplecticNormalExtension [I.Boundaryless]
    [J.Boundaryless] [K.Boundaryless] [CompactSpace Q] [Nonempty Q] [T2Space M]
    [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (hθc : θ.IsClosed) (hσc : σ.IsClosed)
    (i : SmoothEmbedding I J ∞ Q M) (hi : hθ.HasSymplecticTangentImages I i)
    (j : SmoothEmbedding I' K ∞ Q' N) (hj : hσ.HasSymplecticTangentImages I' j)
    (f : Q ≃ₘ⟮I, I'⟯ Q')
    (hf : SmoothForm.mpullback (j ∘ f) (j.contMDiff.comp f.contMDiff) σ =
      SmoothForm.mpullback i i.contMDiff θ)
    (hn : (∞ : ℕ∞ω) ≠ 0)
        (C : ∀ q, i.isImmersion.NormalSpace q hn →L[ℝ] j.isImmersion.NormalSpace (f q) hn)
    (hCinv : ∀ q, (C q).IsInvertible)
    (hCω : ∀ q ν ν', j.symplecticNormalForm hj (f q) hn (C q ν) (C q ν') =
      i.symplecticNormalForm hi q hn ν ν')
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hdim' : Module.finrank ℝ P' = Module.finrank ℝ F - Module.finrank ℝ E')
    (hC : letI := i.normalSpaceFiberBundle hn hdim
      letI := j.normalSpaceFiberBundle hn hdim'
      ContMDiff (I.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, P')) ∞
        (fun p : TotalSpace P (fun q ↦ i.isImmersion.NormalSpace q hn) ↦
          (⟨f p.proj, C p.proj p.snd⟩ : TotalSpace P'
              (fun q' ↦ j.isImmersion.NormalSpace q' hn)))) :
    ∃ (U₀ : Opens M) (U₁ : Opens N) (φ : U₀ ≃ₘ⟮J, K⟯ U₁),
      (∀ q, ∃ h : i q ∈ U₀, (φ ⟨i q, h⟩ : N) = j (f q) ∧
        ∀ v, mfderiv J K φ ⟨i q, h⟩ v = symplecticNormalExtension θ i j hj f hn hn C q v) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal θ := by
  set A := symplecticNormalExtension θ i j hj f hn hn C
  have hg : ContMDiff I K ∞ (j ∘ f) := j.contMDiff.comp f.contMDiff
  have hdg (q : Q) : mfderiv I K (j ∘ f) q = (mfderiv I' K j (f q)).comp (mfderiv I I' f q) :=
    mfderiv_comp q (j.contMDiff.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiableAt (by simp))
  -- The ambient extension realizes the prescribed data: it is smooth in tangent coordinates,
  -- invertible, extends `d (j ∘ f)` and is symplectic.
  have hAsmooth := contMDiff_symplecticNormalExtension i hi j hj f.contMDiff hn C
    (contMDiff_symplecticNormalRepresentative_comp_normalClass i j hj hn C hdim hdim' hC)
  have hA (q : Q) : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i (j ∘ f) A q) q :=
    Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt i (⟨j ∘ f, hg.continuous⟩ : C(Q, N))
      (hg q) A fun _ ↦ hAsmooth _
  have hAinv (q : Q) : (A q).IsInvertible :=
    isInvertible_symplecticNormalExtension i hi j hj f hn hn C q
      (f.isInvertible_mfderiv (by simp)) (hCinv q)
  have hAi (q : Q) : (A q).comp (mfderiv I J i q) = mfderiv I K (j ∘ f) q := by
    ext u
    rw [ContinuousLinearMap.comp_apply, symplecticNormalExtension_mfderiv i hi j hj f hn hn C,
      hdg, ContinuousLinearMap.comp_apply]
  have hAω (q : Q) (v w : TangentSpace J (i q)) :
      SmoothBundleForm.eval₂ σ (j (f q)) (A q v) (A q w) = SmoothBundleForm.eval₂ θ (i q) v w := by
    refine eval₂_symplecticNormalExtension i hi j hj f hn hn C q (fun u w ↦ ?_) (hCω q) v w
    have h := congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ q u w) hf
    simp only [SmoothForm.eval₂_mpullback, hdg, ContinuousLinearMap.comp_apply] at h
    exact h
  -- Realize `A` as the differential of a partial diffeomorphism, then correct it by Moser.
  obtain ⟨Ψ, hsrc, -, -, hval, hd⟩ := i.exists_partialDiffeomorph_mfderiv_eq hg
    (j.isEmbedding.isInducing.comp f.toHomeomorph.isInducing) hA hAinv hAi isOpen_univ
    (subset_univ _) isOpen_univ (subset_univ _)
  obtain ⟨U₀, U₁, φ, hφ, hpull⟩ := SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq
    i hθc (fun q ↦ hθ.nondegenerate_bilinFormAt (i q)) hσc Ψ (fun q ↦ hsrc (mem_range_self q))
    fun q v w ↦ by
      rw [hd q, hval q]
      exact hAω q v w
  refine ⟨U₀, U₁, φ, fun q ↦ ?_, hpull⟩
  obtain ⟨h, hφq, hdφ⟩ := hφ q
  exact ⟨h, hφq.trans (hval q), fun v ↦ (hdφ v).trans (DFunLike.congr_fun (hd q) v)⟩

end Neighborhood

end SmoothEmbedding

end TauCeti

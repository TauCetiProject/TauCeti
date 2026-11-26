/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Topology.VectorBundle.Complex.Structure
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Topology.VectorBundle.Hom

/-!
# The complex normal bundle of an almost complex submanifold

Let `f : M → N` be a smooth embedding into a manifold with a smooth almost complex structure `J`,
and suppose that the tangent spaces of the embedded submanifold are `J`-invariant: `J` maps the
range of `df_x` into itself at every point `x`. This holds for a pseudoholomorphic embedding of a
Riemann surface, `df ∘ j = J ∘ df`
(`TauCeti.SmoothEmbedding.mapsTo_tangentRange_of_isPseudoholomorphicAt`). Then `J` descends to
the intrinsic normal spaces `N_x = T_{f x} N ⧸ range (df_x)`
(`Manifold.IsImmersion.NormalSpace`): the normal complex structure
(`TauCeti.SmoothEmbedding.normalComplexStructureAt`) is the endomorphism of `N_x` with
`J_N [v] = [J v]` for ambient tangent vectors `v`. Its underlying linear map is that of the
quotient almost complex structure (`TauCeti.AlmostComplexStructure.quotient`), as
`TauCeti.SmoothEmbedding.normalComplexStructureAt_toLinearMap` records, so it squares to `-1`. In
other words the normal projection `T_{f x} N → N_x` is complex linear
(`TauCeti.AlmostComplexStructure.isComplexLinearMap_mkQ`).

These complex structures vary smoothly. With the intrinsic normal bundle of a `C^n` embedding,
which is a `C^m` vector bundle for `m + 1 ≤ n`, the map `ν ↦ J_N ν` of total spaces is `C^m`
(`TauCeti.SmoothEmbedding.contMDiff_normalComplexStructureAt`), since on ambient representatives it
is `J` applied along `f`, which is smooth, followed by the smooth normal projection. So `J_N` is a
continuous complex structure on the normal bundle
(`TauCeti.SmoothEmbedding.normalComplexStructure`), and the normal bundle is a complex vector bundle
(`TauCeti.Bundle.ContinuousComplexStructure.Fiber`), whose fibres are the normal spaces with
`J_N` as multiplication by `i`. For an embedded pseudoholomorphic curve `C` in an almost complex
four-manifold it is the complex normal line bundle `N_C` of `C`.

If moreover `J` is orthogonal for a Riemannian metric on `N`, then the orthogonal complement of the
tangent spaces is `J`-invariant, the orthogonal representative of `J_N ν` is `J` applied to that
of `ν` (`TauCeti.SmoothEmbedding.normalRepresentative_normalComplexStructureAt`), and `J_N` is
orthogonal for the induced metric on the normal bundle
(`TauCeti.SmoothEmbedding.inner_normalComplexStructureAt_normalComplexStructureAt`) at every point
where `J` is orthogonal.

## Main definitions

* `TauCeti.SmoothEmbedding.normalComplexStructureAt`: the complex structure of a normal space.
* `TauCeti.SmoothEmbedding.normalComplexStructure`: the normal complex structures as a continuous
  complex structure on the normal bundle.

## Main results

* `TauCeti.SmoothEmbedding.normalComplexStructureAt_normalClass`: `J_N [v] = [J v]`.
* `TauCeti.SmoothEmbedding.normalComplexStructureAt_toLinearMap`: `J_N` is the quotient almost
  complex structure.
* `TauCeti.SmoothEmbedding.normalComplexStructureAt_normalComplexStructureAt`: `J_N (J_N ν) = -ν`.
* `TauCeti.SmoothEmbedding.mapsTo_tangentRange_of_isPseudoholomorphicAt`: the tangent spaces of a
  pseudoholomorphic embedding are `J`-invariant.
* `TauCeti.SmoothEmbedding.contMDiff_normalComplexStructureAt`: `J_N` is `C^m` on total spaces.
* `TauCeti.SmoothEmbedding.contMDiff_normalComplexStructureAt_hom_bundle`: `J_N` is a `C^m`
  section of the endomorphism bundle of the normal bundle.
* `TauCeti.SmoothEmbedding.inner_normalComplexStructureAt_normalComplexStructureAt`: for an
  orthogonal `J`, the normal complex structure is orthogonal for the normal metric.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (the normal bundle of an embedded `J`-holomorphic curve).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (the normal bundle and normal operator of an embedded curve).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold I' ∞ N] {n : ℕ∞ω}

/-! ### The complex structure of a normal space -/

section Fibre

variable (f : SmoothEmbedding I I' n M N) (hn : n ≠ 0) (J : SmoothAlmostComplexStructure I' N)

/-- The complex structure of the normal space of an embedding at `x` whose tangent space is
`J`-invariant: the endomorphism `J_N` of `N_x = T_{f x} N ⧸ range (df_x)` with
`J_N [v] = [J v]` (`TauCeti.SmoothEmbedding.normalComplexStructureAt_normalClass`). -/
def normalComplexStructureAt (x : M) (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
    (f.isImmersion.tangentRange x hn)) : f.isImmersion.NormalSpace x hn →L[ℝ]
        f.isImmersion.NormalSpace x hn :=
  f.isImmersion.normalLiftL x hn
      ((f.isImmersion.normalClassL x hn).comp (J.toEndomorphism (f x))) fun v hv ↦ by
    rw
        [ContinuousLinearMap.comp_apply, Manifold.IsImmersion.normalClassL_apply,
            Manifold.IsImmersion.normalClass_eq_zero_iff]
    exact hJ hv

variable {f hn J}

/-- The normal complex structure sends the normal class of `v` to the normal class of `J v`: the
normal projection is complex linear. -/
@[simp]
theorem normalComplexStructureAt_normalClass {x : M}
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn))
    (v : TangentSpace I' (f x)) :
    f.normalComplexStructureAt hn J x hJ (f.isImmersion.normalClass x hn v) =
      f.isImmersion.normalClass x hn (J (f x) v) := by
  rw
      [normalComplexStructureAt, Manifold.IsImmersion.normalLiftL_normalClass,
          ContinuousLinearMap.comp_apply,
    Manifold.IsImmersion.normalClassL_apply]

/-- The normal complex structure is the almost complex structure that `J` induces on the
quotient `N_x = T_{f x} N ⧸ range (df_x)`. -/
theorem normalComplexStructureAt_toLinearMap {x : M}
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn)) :
    (f.normalComplexStructureAt hn J x hJ).toLinearMap =
      ((J.almostComplexStructureAt (f x)).quotient (f.isImmersion.tangentRange x hn)
        fun _ hv ↦ by
          rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
          exact hJ hv).toLinearMap := by
  refine LinearMap.ext fun ν ↦ ?_
  obtain ⟨v, rfl⟩ := f.isImmersion.normalClass_surjective x hn ν
  rw
      [ContinuousLinearMap.coe_coe, normalComplexStructureAt_normalClass,
          Manifold.IsImmersion.normalClass_def]
  refine ((AlmostComplexStructure.quotient_mk _ _ _ v).trans ?_).symm
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  exact (Submodule.mkQ_apply _ _).symm

/-- The normal complex structure squares to `-1`. -/
@[simp]
theorem normalComplexStructureAt_normalComplexStructureAt {x : M}
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn))
    (ν : f.isImmersion.NormalSpace x hn) :
    f.normalComplexStructureAt hn J x hJ (f.normalComplexStructureAt hn J x hJ ν) = -ν := by
  have h := LinearMap.congr_fun (normalComplexStructureAt_toLinearMap hJ)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h, h]
  exact AlmostComplexStructure.apply_apply _ ν

/-- The normal complex structure squares to `-1`, as an identity of endomorphisms. -/
theorem normalComplexStructureAt_comp_self {x : M}
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn)) :
    (f.normalComplexStructureAt hn J x hJ).comp (f.normalComplexStructureAt hn J x hJ) =
      -ContinuousLinearMap.id ℝ (f.isImmersion.NormalSpace x hn) :=
  ContinuousLinearMap.ext fun ν ↦ normalComplexStructureAt_normalComplexStructureAt hJ ν

end Fibre

/-! ### Pseudoholomorphic embeddings -/

section Pseudoholomorphic

variable [IsManifold I ∞ M] {f : SmoothEmbedding I I' n M N} (hn : n ≠ 0)
  {j : SmoothAlmostComplexStructure I M} {J : SmoothAlmostComplexStructure I' N} {x : M}

/-- The tangent space at `x` of a pseudoholomorphic embedding is `J`-invariant. -/
theorem mapsTo_tangentRange_of_isPseudoholomorphicAt (hf : IsPseudoholomorphicAt j J f x) :
    MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn) := by
  -- By the Cauchy–Riemann equation `df ∘ j = J ∘ df`, `J (df w)` is the tangent vector `df (j w)`.
  rintro _ ⟨w, rfl⟩
  exact ⟨j x w, hf.mfderiv_apply_commute w⟩

end Pseudoholomorphic

/-! ### Smoothness of the normal complex structure -/

section Smooth

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ P]
  {m : ℕ∞ω} [ENat.LEInfty m] [IsManifold I (m + 1) M]
  (f : SmoothEmbedding I I' n M N) (hn : n ≠ 0) (J : SmoothAlmostComplexStructure I' N)

/-- The normal complex structure of an embedding whose tangent spaces are `J`-invariant is `C^m`
on the total space of its normal bundle when the embedding is `C^n` with `m + 1 ≤ n`. -/
theorem contMDiff_normalComplexStructureAt (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) m
      (fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' P (E := fun x ↦ f.isImmersion.NormalSpace x hn) p.proj
          (f.normalComplexStructureAt hn J p.proj (hJ p.proj) p.snd)) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  -- `N` is `C^∞` and `m ≤ ∞`, so `N` is `C^(m + 1)`, as the normal bundle API requires.
  have : IsManifold I' (m + 1) N :=
    .of_le ((add_le_add (ENat.LEInfty.out (m := m)) le_rfl).trans (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞))
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  -- On ambient representatives `J_N` is `J` applied along `f`, followed by the normal projection.
  -- On the ambient tangent bundle, `J` is `C^m` on total spaces; pull it back along `f`.
  have hJtot : ContMDiff (I'.prod 𝓘(ℝ, V)) (I'.prod 𝓘(ℝ, V)) m
      fun p : TotalSpace V (TangentSpace I' : N → Type _) ↦
        TotalSpace.mk' V p.proj (J p.proj p.snd) :=
    J.contMDiff_apply (V := fun p : TangentBundle I' N ↦ p.snd) contMDiff_id
  have hT := Bundle.Pullback.contMDiff_fiberwise (fun y ↦ J y) hJtot f
    (f.contMDiff.of_le ((le_add_right le_rfl).trans hm))
  refine ((f.contMDiff_normalQuotientMap hn hm hdim).comp hT).congr fun p ↦ ?_
  -- Taking normal classes keeps the base point, so both sides lie over `p.proj`.
  have hq := f.normalQuotientMap_apply (K := P) hn p
  simp only [Function.comp_apply]
  generalize f.normalQuotientMap hn p = r at hq ⊢
  subst hq
  rw [normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' P (E := fun x ↦ f.isImmersion.NormalSpace x hn) p.proj)
    (normalComplexStructureAt_normalClass (hJ p.proj) p.snd)

/-- The normal complex structure of an embedding whose tangent spaces are `J`-invariant is a `C^m`
section of the endomorphism bundle of its normal bundle when the embedding is `C^n` with
`m + 1 ≤ n`. -/
theorem contMDiff_normalComplexStructureAt_hom_bundle (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiff I (I.prod 𝓘(ℝ, P →L[ℝ] P)) m
      (fun x ↦ TotalSpace.mk' (P →L[ℝ] P)
        (E := fun x ↦ f.isImmersion.NormalSpace x hn →L[ℝ] f.isImmersion.NormalSpace x hn) x
        (f.normalComplexStructureAt hn J x (hJ x))) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact (contMDiff_hom_bundle_iff _).2 (f.contMDiff_normalComplexStructureAt hn J hm hdim hJ)

/-- The normal complex structures of an embedding whose tangent spaces are `J`-invariant, as a
continuous complex structure on its normal bundle. With them the normal bundle is a complex vector
bundle (`TauCeti.Bundle.ContinuousComplexStructure.Fiber`). -/
def normalComplexStructure [IsManifold I 1 M]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    Bundle.ContinuousComplexStructure P (fun x ↦ f.isImmersion.NormalSpace x hn) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  { toFun x := f.normalComplexStructureAt hn J x (hJ x)
    comp_self x := normalComplexStructureAt_comp_self (hJ x)
    continuous := by
      have : IsManifold I (0 + 1) M := by rwa [zero_add]
      have hm : (0 : ℕ∞ω) + 1 ≤ n := by
        rw [zero_add]
        exact ENat.one_le_iff_ne_zero_withTop.2 hn
      exact (continuous_hom_bundle_iff _).2
        (f.contMDiff_normalComplexStructureAt (m := 0) hn J hm hdim hJ).continuous }

/-- The continuous complex structure on the normal bundle is the normal complex structure on each
fibre. -/
@[simp]
theorem normalComplexStructure_apply [IsManifold I 1 M]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hJ : ∀ x, MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn))
        (x : M)
    (ν : f.isImmersion.NormalSpace x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.normalComplexStructure hn J hdim hJ x ν = f.normalComplexStructureAt hn J x (hJ x) ν :=
  (rfl)

end Smooth

/-! ### Orthogonal almost complex structures -/

section Hermitian

variable [FiniteDimensional ℝ V] [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  {f : SmoothEmbedding I I' n M N} {hn : n ≠ 0} {J : SmoothAlmostComplexStructure I' N} {x : M}

/-- If `J` is orthogonal at `f x` and the tangent space at `x` is `J`-invariant, then the
orthogonal representative of `J_N ν` is `J` applied to the orthogonal representative of `ν`: the
orthogonal complement of the tangent space is `J`-invariant. -/
theorem normalRepresentative_normalComplexStructureAt
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn))
    (hJg : ∀ v w : TangentSpace I' (f x), inner ℝ (J (f x) v) (J (f x) w) = inner ℝ v w)
    (ν : f.isImmersion.NormalSpace x hn) :
    f.normalRepresentative x hn (f.normalComplexStructureAt hn J x hJ ν) =
      J (f x) (f.normalRepresentative x hn ν) := by
  refine ((f.normalRepresentative_eq_iff x hn _ _).2 ⟨?_, ?_⟩)
  · rw [Submodule.mem_orthogonal]
    intro u hu
    -- `⟪u, J r⟫ = ⟪J u, J (J r)⟫ = -⟪J u, r⟫`, and `J u` is again tangent.
    rw [← hJg]
    simp only [SmoothAlmostComplexStructure.apply_apply, inner_neg_right,
      Submodule.inner_right_of_mem_orthogonal (hJ hu)
        (f.normalRepresentative_mem_orthogonal x hn ν), neg_zero]
  · rw [← normalComplexStructureAt_normalClass hJ, normalClass_normalRepresentative]

/-- If `J` is orthogonal at `f x` and the tangent space at `x` is `J`-invariant, then the normal
complex structure is orthogonal for the induced metric on the normal bundle. -/
theorem inner_normalComplexStructureAt_normalComplexStructureAt
    (hJ : MapsTo (J (f x)) (f.isImmersion.tangentRange x hn) (f.isImmersion.tangentRange x hn))
    (hJg : ∀ v w : TangentSpace I' (f x), inner ℝ (J (f x) v) (J (f x) w) = inner ℝ v w)
    (ν μ : f.isImmersion.NormalSpace x hn) :
    (f.normalRiemannianMetric hn).inner x (f.normalComplexStructureAt hn J x hJ ν)
        (f.normalComplexStructureAt hn J x hJ μ) =
      (f.normalRiemannianMetric hn).inner x ν μ := by
  simp only [normalRiemannianMetric_inner, normalRepresentative_normalComplexStructureAt hJ hJg,
    hJg]

end Hermitian

end TauCeti.SmoothEmbedding

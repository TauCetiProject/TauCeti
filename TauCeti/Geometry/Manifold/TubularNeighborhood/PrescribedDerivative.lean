/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Geometry.Manifold.Diffeomorph.Empty
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Lift
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Tubular neighbourhood diffeomorphisms with prescribed ambient derivative

Let `i : Q → M` be a `C^n` embedding of a finite-dimensional boundaryless manifold into a
finite-dimensional Hausdorff second-countable smooth boundaryless manifold, let `g : Q → N` be a
`C^m` topological embedding (`1 ≤ m ≤ ∞`, `m + 1 ≤ n`) into another finite-dimensional Hausdorff
second-countable smooth boundaryless manifold, and let
`A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q)` be a `C^m` family of continuous
linear equivalences extending the differential along `Q` in the sense that `A q ∘ di_q = dg_q` for
every `q : Q` (where `C^m` regularity of `A` is `C^m` regularity of its coordinate expressions
`inTangentCoordinates`).

This file proves that `A` is realized as the ambient differential along `Q` of a `C^m`
diffeomorphism `Φ : U ≃ₘ^m⟮I, I'⟯ V` between open neighbourhoods `U ⊆ O_M` of `range i` and
`V ⊆ O_N` of `range g`, sending `i q` to `g q`
(`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq_subset` and
`Manifold.IsSmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq`). Neither compactness of `Q` nor
closedness of the embedded images is required.

In differential and symplectic topology, an embedding `i : Q → M` controls the pullback `i^* σ` of
an ambient differential form only on tangent vectors to `Q`, whereas relative Moser and Weinstein
Lagrangian neighbourhood arguments require an ambient diffeomorphism whose pulled-back form agrees
with `σ` on the **full ambient tangent spaces** `T_(i q) M` along `i(Q)`. Realizing a
form-intertwining family `A` as the ambient differential of `Φ` along `Q` upgrades linear normal or
polarization data along `Q` to full ambient differential-form agreement along `i(Q)`
(`TauCeti.SmoothForm.mpullback_apply_eq_of_mfderiv_eq`).

## Method of proof

Choose auxiliary smooth Riemannian metrics on `M` and `N`. On the intrinsic normal bundle `ν` of
`i`, the Riemannian normal exponential of `i` gives a partial diffeomorphism `Φ₀` from an open
neighbourhood of the zero section onto an open subset of `O_M`, whose differential at `0_q` sends
`(u, v)` to `di_q u + r_q v`, where `r_q` is the orthogonal normal representative in `T_(i q) M`.

Transporting `r_q v` to `T_(g q) N` via `A q` and exponentiating in `N` defines the **twisted
normal exponential** `p ↦ exp^N_(g p.proj) (A p.proj (r_(p.proj) p.2))`
(`TauCeti.SmoothEmbedding.twistedNormalExp`), obtained from the general bundle-lift exponential
`TauCeti.Bundle.liftExp`. Its differential at `0_q` sends `(u, v)` to `dg_q u + A q (r_q v)`; when
`A q ∘ di_q = dg_q`, this equals `A q ∘ d(i.normalExp)_(0_q)`, which is invertible. Since the
restriction of the twisted normal exponential to the zero section is the embedding `g`,
`TauCeti.Bundle.exists_partialDiffeomorph_liftExp_subset` upgrades it to a partial diffeomorphism
`Φ₁` near the zero section with target in `O_N`. The composite `Φ₀.symm.trans Φ₁` restricts to the
desired diffeomorphism of open neighbourhoods.

Conversely, differentiating a smooth map on an open neighbourhood along `i` produces a `C^m` family
of ambient differentials (continuous linear maps) in `inTangentCoordinates` extending `dg`
(`TauCeti.Manifold.contMDiffAt_inTangentCoordinates_subtype_val_comp_mfderiv`,
`TauCeti.Manifold.mfderiv_comp_mfderiv_subtype_val_comp`), and over finite-dimensional tangent
fibres regularity in `inTangentCoordinates` is intrinsically characterized by sending `C^m` tangent
lifts along the source map to `C^m` tangent lifts along the target map
(`TauCeti.Manifold.contMDiffAt_inTangentCoordinates_iff`).

## Acknowledgements

The twisted normal-exponential API (`twistedNormalExpDomain`, `twistedNormalExp`, and their
regularity, differential, and coordinate lemmas) adapts and shares `TauCeti.Bundle.liftExp` with
`SmoothEmbedding.normalExp*` in
`TauCeti/Geometry/Manifold/TubularNeighborhood/Riemannian/Basic.lean`, `Regularity.lean`,
`Differential.lean`, and `Coordinates.lean`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4.
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
-/

public noncomputable section

open Bundle Manifold Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

section TwistedNormalExpDefs

variable {F E E' P K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace K] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y)]
  {n : ℕ∞ω}

/-- The natural domain in the intrinsic normal bundle of `i` on which the orthogonal normal
representative, transported along `A` into `T_(g q) N`, lies in the Riemannian exponential domain
of `N`. -/
def twistedNormalExpDomain (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) :
    Set (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
  TauCeti.Bundle.liftExpDomain g (fun q ↦ (A q).comp (i.normalRepresentative q hn))

/-- The **twisted normal exponential** of an embedding `i : Q → M` along a map `g : Q → N` and a
family `A q : T_(i q) M →L[ℝ] T_(g q) N`: it sends a normal class `(q, v)` to the Riemannian
exponential at `g q` of `A q` applied to the orthogonal representative of `v` in `T_(i q) M`. -/
def twistedNormalExp (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) : N :=
  TauCeti.Bundle.liftExp g (fun q ↦ (A q).comp (i.normalRepresentative q hn)) p

/-- Membership in `twistedNormalExpDomain` unpacks to membership of the transported orthogonal
normal representative in `Manifold.expDomain`. -/
theorem mem_twistedNormalExpDomain (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) :
    p ∈ i.twistedNormalExpDomain (P := P) hn A ↔
      A p.proj (i.normalRepresentative p.proj hn p.2) ∈ Manifold.expDomain I' N (g p.proj) :=
  TauCeti.Bundle.mem_liftExpDomain g (fun q ↦ (A q).comp (i.normalRepresentative q hn)) p

/-- Evaluating `twistedNormalExp` exponentiates the `A`-image of the orthogonal normal
representative at `g p.proj`. -/
theorem twistedNormalExp_apply (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) :
    i.twistedNormalExp (P := P) hn A p =
      Manifold.riemannianExp I' N (g p.proj) (A p.proj (i.normalRepresentative p.proj hn p.2)) :=
  TauCeti.Bundle.liftExp_apply g (fun q ↦ (A q).comp (i.normalRepresentative q hn)) p

/-- Every point of the zero section of the normal bundle lies in `twistedNormalExpDomain`. -/
@[simp]
theorem zeroSection_mem_twistedNormalExpDomain
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0)
    {g : Q → N} (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) (q : Q) :
    zeroSection P (fun q ↦ i.NormalSpace q hn) q ∈ i.twistedNormalExpDomain (P := P) hn A :=
  TauCeti.Bundle.zeroSection_mem_liftExpDomain g
    (fun q ↦ (A q).comp (i.normalRepresentative q hn)) q

/-- On the zero section of the normal bundle, the twisted normal exponential agrees with `g`. -/
@[simp]
theorem twistedNormalExp_zeroSection [I'.Boundaryless] [T2Space N]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) (q : Q) :
    i.twistedNormalExp (P := P) hn A (zeroSection P (fun q ↦ i.NormalSpace q hn) q) = g q :=
  TauCeti.Bundle.liftExp_zeroSection g (fun q ↦ (A q).comp (i.normalRepresentative q hn)) q

end TwistedNormalExpDefs

section Representative

variable {F E E' P K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace K] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  {n m : ℕ∞ω}
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]

/-- Transporting the orthogonal normal representative of `i` by a `C^m` family `A` (in
`inTangentCoordinates`) gives a `C^m` map from the intrinsic normal bundle of `i` into `TN`. -/
theorem contMDiff_totalSpaceMk_apply_normalRepresentative
    [IsManifold J (m + 1) Q] [IsManifold I (m + 1) M]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g A q₀) q₀) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, E')) m
      (fun p : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦
        (⟨g p.proj, A p.proj (i.normalRepresentative p.proj hn p.2)⟩ : TangentBundle I' N)) := by
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  intro p₀
  have hbase : ContMDiffAt (J.prod 𝓘(ℝ, P)) J m
      (π P (fun q ↦ i.NormalSpace q hn)) p₀ :=
    contMDiff_proj (fun q ↦ i.NormalSpace q hn) p₀
  have hAp : ContMDiffAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, E →L[ℝ] E') m
      (fun p : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E' (TangentSpace I')
          (i p₀.proj) (i p.proj) (g p₀.proj) (g p.proj) (A p.proj)) p₀ :=
    (hA p₀.proj).comp p₀ hbase
  have hrep := i.contMDiff_normalRepresentative (m := m) hn hm hdim p₀
  exact ContMDiffAt.clm_apply_of_inCoordinates hAp hrep ((hg p₀.proj).comp p₀ hbase)

end Representative

section TwistedNormalExp

variable {F E E' P K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace K] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [I'.Boundaryless] [T2Space N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y)]
  {n m : ℕ∞ω}

/-- The domain `twistedNormalExpDomain` is open in the intrinsic normal bundle when `g` and `A`
are continuous (`C^0`). -/
theorem isOpen_twistedNormalExpDomain [IsManifold J 1 Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' 0 g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') 0
      (inTangentCoordinates I I' i g A q₀) q₀) :
    letI := i.normalSpaceFiberBundle hn hdim
    IsOpen (i.twistedNormalExpDomain (P := P) hn A) := by
  have : IsManifold J (0 + 1) Q := by simpa using (inferInstance : IsManifold J 1 Q)
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (n := ∞) zero_le
  let := i.normalSpaceFiberBundle hn hdim
  exact TauCeti.Bundle.isOpen_liftExpDomain (P := P) (g := g)
    (L := fun q ↦ (A q).comp (i.normalRepresentative q hn))
    (i.contMDiff_totalSpaceMk_apply_normalRepresentative (m := 0) hn
      (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim hg hA).continuous

/-- The twisted normal exponential is `C^m` (`m ≤ ∞`) on its natural open domain for a `C^n`
embedding `i` with `m + 1 ≤ n` and `C^m` data `g, A`. -/
theorem contMDiffOn_twistedNormalExp [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g A q₀) q₀) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    ContMDiffOn (J.prod 𝓘(ℝ, P)) I' m (i.twistedNormalExp (P := P) hn A)
      (i.twistedNormalExpDomain (P := P) hn A) := by
  have hm' : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold I (m + 1) M := .of_le hm'
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x) :=
    .of_le ENat.LEInfty.out
  let := i.normalSpaceFiberBundle hn hdim
  exact TauCeti.Bundle.contMDiffOn_liftExp (P := P) (g := g)
    (L := fun q ↦ (A q).comp (i.normalRepresentative q hn))
    (i.contMDiff_totalSpaceMk_apply_normalRepresentative hn hm hdim hg hA)

/-- Under the canonical splitting of the tangent space along the zero section of the normal bundle
of `i`, the differential of `twistedNormalExp` sends `(u, v)` to
`dg_q u + A q (i.normalRepresentative q hn v)`. -/
theorem mfderiv_twistedNormalExp_zeroSection_apply [IsManifold J (1 + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (h2 : 1 + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' 1 g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') 1
      (inTangentCoordinates I I' i g A q₀) q₀)
    (q : Q) (u : TangentSpace J q) (v : i.NormalSpace q hn) :
    haveI : IsManifold J 1 Q := .of_le (n := 1 + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    mfderiv (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q)
        ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
      mfderiv J I' g q u + A q (i.normalRepresentative q hn v) := by
  have : IsManifold J 1 Q := .of_le (n := 1 + 1) le_add_self
  have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle (m := 1) hn h2 hdim
  exact TauCeti.Bundle.mfderiv_liftExp_zeroSection_apply (P := P) (g := g)
    (L := fun q ↦ (A q).comp (i.normalRepresentative q hn))
    (i.contMDiff_totalSpaceMk_apply_normalRepresentative (m := 1) hn h2 hdim hg hA) q u v

/-- When `A q ∘L mfderiv J I i q = mfderiv J I' g q`, the differential of `twistedNormalExp` at
`0_q` factors as `A q` composed with the differential of `i.normalExp` at `0_q`. -/
theorem mfderiv_twistedNormalExp_zeroSection_eq_comp [I.Boundaryless] [T2Space M]
    [IsManifold J (1 + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (h2 : 1 + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' 1 g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') 1
      (inTangentCoordinates I I' i g A q₀) q₀)
    {q : Q} (hAq : A q ∘L mfderiv J I i q = mfderiv J I' g q) :
    haveI : IsManifold J 1 Q := .of_le (n := 1 + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    (mfderiv (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :
          TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
            TangentSpace I' (g q)) =
      A q ∘L (mfderiv (J.prod 𝓘(ℝ, P)) I (i.normalExp (P := P) hn)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :
          TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
            TangentSpace I (i q)) := by
  have : IsManifold J 1 Q := .of_le (n := 1 + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  -- Name the two differentials at `g q` and `i q` so their target tangent spaces match
  -- syntactically under `implicit` transparency.
  let D₁ : TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
      TangentSpace I' (g q) :=
    mfderiv (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q)
  let D₀ : TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
      TangentSpace I (i q) :=
    mfderiv (J.prod 𝓘(ℝ, P)) I (i.normalExp (P := P) hn)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q)
  have hD₁ (u : TangentSpace J q) (v : i.NormalSpace q hn) :
      D₁ ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
        mfderiv J I' g q u + A q (i.normalRepresentative q hn v) :=
    i.mfderiv_twistedNormalExp_zeroSection_apply hn h2 hdim hg hA q u v
  have hD₀ (u : TangentSpace J q) (v : i.NormalSpace q hn) :
      D₀ ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
        mfderiv J I i q u + i.normalRepresentative q hn v :=
    i.mfderiv_normalExp_zeroSection_apply hn h2 hdim q u v
  ext w
  obtain ⟨⟨u, v⟩, rfl⟩ :=
    (Bundle.zeroSectionTangentEquiv (I := J) (F := P)
      (V := fun q ↦ i.NormalSpace q hn) q).symm.surjective w
  have hAq_u : A q (mfderiv J I i q u) = mfderiv J I' g q u := DFunLike.congr_fun hAq u
  exact (hD₁ u v).trans <|
    (congrArg (· + A q (i.normalRepresentative q hn v)) hAq_u.symm).trans <|
      (map_add (A q) _ _).symm.trans (congrArg (A q) (hD₀ u v).symm)

/-- When `A q` is invertible and `A q ∘L mfderiv J I i q = mfderiv J I' g q`, the twisted normal
exponential is a `C^m` (`1 ≤ m ≤ ∞`) local diffeomorphism at `0_q`. -/
theorem isLocalDiffeomorphAt_twistedNormalExp_zeroSection [J.Boundaryless] [I.Boundaryless]
    [T2Space M] [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) q₀) q₀)
    {q : Q}
    (hAq : (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) ∘L mfderiv J I i q =
      mfderiv J I' g q) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I' m
      (i.twistedNormalExp (P := P) hn
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))))
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q) := by
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have hminfty : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J m Q := .of_le (n := m + 1) le_self_add
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
  have : IsManifold I (m + 1) M := .of_le (n := ∞) hminfty
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x) :=
    .of_le ENat.LEInfty.out
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle hn hm hdim
  obtain ⟨e₀, he₀⟩ := i.isInvertible_mfderiv_normalExp_zeroSection hn (h2m.trans hm) hdim q
  have hcomp := i.mfderiv_twistedNormalExp_zeroSection_eq_comp hn (h2m.trans hm) hdim
    (hg.of_le hm1) (fun q₀ ↦ (hA q₀).of_le hm1) hAq
  have hinv : (mfderiv (J.prod 𝓘(ℝ, P)) I'
      (i.twistedNormalExp (P := P) hn
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))))
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q)).IsInvertible := by
    refine ⟨e₀.trans (A q), ?_⟩
    ext w
    exact (congrArg (A q) (DFunLike.congr_fun he₀ w)).trans (DFunLike.congr_fun hcomp.symm w)
  exact TauCeti.Bundle.isLocalDiffeomorphAt_liftExp_zeroSection (P := P) (g := g)
    (L := fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)).comp
      (i.normalRepresentative q hn)) hm1
    (i.contMDiff_totalSpaceMk_apply_normalRepresentative hn hm hdim hg hA) hinv

/-- When `Q` is nonempty and `g : Q → N` is a `C^m` topological embedding (`1 ≤ m ≤ ∞`,
`m + 1 ≤ n`), the twisted normal exponential restricts to a single `C^m` partial diffeomorphism on
an open neighbourhood of the zero section with target inside any prescribed open neighbourhood `O`
of `range g`. -/
theorem exists_partialDiffeomorph_twistedNormalExp_subset [J.Boundaryless] [I.Boundaryless]
    [T2Space M] [SecondCountableTopology N] [Nonempty Q]
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g) (hg_emb : IsEmbedding g)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) ∘L mfderiv J I i q =
        mfderiv J I' g q)
    {O : Set N} (hO : IsOpen O) (hgO : range g ⊆ O) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    ∃ Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I'
        (TotalSpace P (fun q ↦ i.NormalSpace q hn)) N m,
      (∀ q, zeroSection P (fun q ↦ i.NormalSpace q hn) q ∈ Φ.source) ∧
      Φ.source ⊆ i.twistedNormalExpDomain hn
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) ∧
      Φ.target ⊆ O ∧
      ⇑Φ = i.twistedNormalExp hn
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) := by
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have hminfty : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J m Q := .of_le (n := m + 1) le_self_add
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
  have : IsManifold I (m + 1) M := .of_le (n := ∞) hminfty
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x) :=
    .of_le ENat.LEInfty.out
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle hn hm hdim
  have hinv : ∀ q : Q, (mfderiv (J.prod 𝓘(ℝ, P)) I'
      (i.twistedNormalExp (P := P) hn
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))))
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q)).IsInvertible := by
    intro q
    obtain ⟨e₀, he₀⟩ := i.isInvertible_mfderiv_normalExp_zeroSection hn (h2m.trans hm) hdim q
    have hcomp := i.mfderiv_twistedNormalExp_zeroSection_eq_comp hn (h2m.trans hm) hdim
      (hg.of_le hm1) (fun q₀ ↦ (hA q₀).of_le hm1) (hAi q)
    refine ⟨e₀.trans (A q), ?_⟩
    ext w
    exact (congrArg (A q) (DFunLike.congr_fun he₀ w)).trans (DFunLike.congr_fun hcomp.symm w)
  obtain ⟨Φ, hzero, hsrc, htgt, -, hΦ⟩ :=
    TauCeti.Bundle.exists_partialDiffeomorph_liftExp_subset (P := P) (g := g)
      (L := fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)).comp
        (i.normalRepresentative q hn)) hm1 hg_emb
      (i.contMDiff_totalSpaceMk_apply_normalRepresentative hn hm hdim hg hA) hinv hO hgO
  exact ⟨Φ, hzero, hsrc, htgt, hΦ⟩

end TwistedNormalExp

section PrescribedDerivative

variable {F E E' K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace K] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [J.Boundaryless] [I.Boundaryless] [I'.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [T2Space N]
  [SecondCountableTopology N]
  {n m : ℕ∞ω}

/-- **Partial diffeomorphism with prescribed ambient derivative.** Given a `C^n` embedding
`i : Q → M` of a nonempty finite-dimensional boundaryless manifold into a finite-dimensional
Hausdorff second-countable smooth boundaryless manifold `M`, a `C^m` topological embedding
`g : Q → N` (`1 ≤ m ≤ ∞`, `m + 1 ≤ n`) into another finite-dimensional Hausdorff second-countable
smooth boundaryless manifold `N`, and a `C^m` family of continuous linear equivalences
`A q : T_(i q) M ≃L[ℝ] T_(g q) N` in `inTangentCoordinates` satisfying `A q ∘ di_q = dg_q`, there
exists a `C^m` partial diffeomorphism `Ψ` from `M` to `N` whose source lies in `O_M` and contains
`range i`, whose target lies in `O_N`, and which satisfies `Ψ (i q) = g q` and `dΨ_(i q) = A q`
for every `q : Q`. -/
theorem exists_partialDiffeomorph_mfderiv_eq_subset [Nonempty Q]
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    {g : Q → N} (hg : ContMDiff J I' m g) (hg_emb : IsEmbedding g)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) ∘L mfderiv J I i q =
        mfderiv J I' g q)
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hgO : range g ⊆ O_N) :
    ∃ Ψ : PartialDiffeomorph I I' M N m,
      Ψ.source ⊆ O_M ∧ Ψ.target ⊆ O_N ∧
      ∀ q : Q, i q ∈ Ψ.source ∧ Ψ (i q) = g q ∧
        mfderiv I I' Ψ (i q) = (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) := by
  have hn : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hm)
  have hm0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  have := i.finiteDimensional_tangentSpace q₀ hn
  have : FiniteDimensional ℝ F := (tangentSpaceCastModel J q₀).toLinearEquiv.finiteDimensional
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace H' := I'.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  -- Choose auxiliary smooth Riemannian metrics on `M` and `N`.
  obtain ⟨gM⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  obtain ⟨gN⟩ := nonempty_contMDiffRiemannianMetric (IB := I') (n := ⊤) (F := E')
    (E := fun y : N ↦ TangentSpace I' y)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gM.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle gM
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) := ⟨gN.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ F))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F :=
    finrank_euclideanSpace_fin
  let := i.normalSpaceFiberBundle hn hdim
  obtain ⟨Φ₀, hzero₀, -, htarget₀, -, hΦ₀⟩ :=
    i.exists_partialDiffeomorph_normalExp_subset (P := P) (m := m) hn hm hm1 hdim hOM hiO
  obtain ⟨Φ₁, hzero₁, -, htarget₁, hΦ₁⟩ :=
    i.exists_partialDiffeomorph_twistedNormalExp_subset (P := P) (m := m)
      hn hm hm1 hdim hg hg_emb A hA hAi hON hgO
  let Ψ := Φ₀.symm.trans Φ₁
  refine ⟨Ψ, fun _ hx ↦ htarget₀ hx.1, fun _ hy ↦ htarget₁ hy.1, fun q ↦ ?_⟩
  let z₀ := zeroSection P (fun q ↦ i.NormalSpace q hn) q
  have hΦ₀z : Φ₀ z₀ = i q := by rw [hΦ₀, i.normalExp_zeroSection]
  have hΦ₁z : Φ₁ z₀ = g q := by rw [hΦ₁, i.twistedNormalExp_zeroSection]
  have hiq_src : i q ∈ Ψ.source :=
    hΦ₀z ▸ Φ₀.apply_mem_symm_trans_source Φ₁ (hzero₀ q) (hzero₁ q)
  have hΨ_iq : Ψ (i q) = g q := by
    rw [← hΦ₀z, Φ₀.symm_trans_apply_apply Φ₁ (hzero₀ q), hΦ₁z]
  have hcomp_exp := i.mfderiv_twistedNormalExp_zeroSection_eq_comp hn (h2m.trans hm) hdim
    (hg.of_le hm1) (fun q₀ ↦ (hA q₀).of_le hm1) (hAi q)
  have hcomp_Φ : (mfderiv (J.prod 𝓘(ℝ, P)) I' Φ₁ z₀ :
      TangentSpace (J.prod 𝓘(ℝ, P)) z₀ →L[ℝ] TangentSpace I' (g q)) =
    (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)).comp
      (mfderiv (J.prod 𝓘(ℝ, P)) I Φ₀ z₀ :
        TangentSpace (J.prod 𝓘(ℝ, P)) z₀ →L[ℝ] TangentSpace I (i q)) := by
    rw [hΦ₁, hΦ₀]
    exact hcomp_exp
  exact ⟨hiq_src, hΨ_iq,
    Φ₀.mfderiv_symm_trans_eq_of_comp Φ₁ hm0 (hzero₀ q) (hzero₁ q) hΦ₀z hΦ₁z hcomp_Φ⟩

/-- **Tubular neighbourhood diffeomorphism with prescribed ambient derivative.** Given a `C^n`
embedding `i : Q → M` of a finite-dimensional boundaryless manifold into a finite-dimensional
Hausdorff second-countable smooth boundaryless manifold `M`, a `C^m` topological embedding
`g : Q → N` (`1 ≤ m ≤ ∞`, `m + 1 ≤ n`) into another finite-dimensional Hausdorff second-countable
smooth boundaryless manifold `N`, and a `C^m` family of continuous linear equivalences
`A q : T_(i q) M ≃L[ℝ] T_(g q) N` in `inTangentCoordinates` satisfying `A q ∘ di_q = dg_q`, there
exist open neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_N` of `range g` and a `C^m`
diffeomorphism `Φ : U ≃ₘ^m⟮I, I'⟯ V` sending `i q` to `g q` with ambient differential `A q` at
`i q` for every `q : Q`. Neither compactness nor nonemptiness of `Q` is required. -/
theorem exists_diffeomorph_opens_mfderiv_eq_subset
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    {g : Q → N} (hg : ContMDiff J I' m g) (hg_emb : IsEmbedding g)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) ∘L mfderiv J I i q =
        mfderiv J I' g q)
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hgO : range g ⊆ O_N) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ^m⟮I, I'⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set N) ⊆ O_N ∧
      ∀ q : Q, ∃ hq : i q ∈ U, (Φ ⟨i q, hq⟩ : N) = g q ∧
        mfderiv I I' (fun x : U ↦ (Φ x : N)) ⟨i q, hq⟩ =
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) := by
  cases isEmpty_or_nonempty Q with
  | inl hQ =>
    have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.2⟩
    have : IsEmpty (⊥ : Opens N) := ⟨fun y ↦ y.2⟩
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, empty_subset O_M, empty_subset O_N,
      fun q ↦ (hQ.false q).elim⟩
  | inr hQ =>
    obtain ⟨Ψ, hsrc, htgt, hΨ⟩ :=
      i.exists_partialDiffeomorph_mfderiv_eq_subset hm hm1 hg hg_emb A hA hAi hOM hiO hON hgO
    refine ⟨⟨Ψ.source, Ψ.open_source⟩, ⟨Ψ.target, Ψ.open_target⟩,
      Ψ.toDiffeomorphSourceTarget, hsrc, htgt, fun q ↦ ?_⟩
    obtain ⟨hq, hval, hd⟩ := hΨ q
    refine ⟨hq, (Ψ.toDiffeomorphSourceTarget_apply_coe ⟨i q, hq⟩).trans hval, ?_⟩
    have hcoe : (fun x : (⟨Ψ.source, Ψ.open_source⟩ : Opens M) ↦
        (Ψ.toDiffeomorphSourceTarget x : N)) = Ψ ∘ Subtype.val :=
      funext Ψ.toDiffeomorphSourceTarget_apply_coe
    rw [hcoe]
    ext u
    have hsub := TauCeti.Manifold.mfderiv_comp_subtype_val_apply (J := I) (I := I')
      (U := (⟨Ψ.source, Ψ.open_source⟩ : Opens M)) (f := Ψ) (x := ⟨i q, hq⟩) u
    exact hsub.trans (DFunLike.congr_fun hd u)

end PrescribedDerivative

end TauCeti.SmoothEmbedding

namespace Manifold.IsSmoothEmbedding

variable {F F' E E' K K' H H' Q Q' M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace K] [TopologicalSpace K'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {J' : ModelWithCorners ℝ F' K'}
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [J.Boundaryless] [I.Boundaryless] [I'.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace Q'] [ChartedSpace K' Q']
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [T2Space N]
  [SecondCountableTopology N]
  {n m : ℕ∞ω}

/-- **Neighbourhood diffeomorphism with prescribed ambient derivative, inside prescribed open
sets.** Let `i : Q → M` and `j : Q' → N` be `C^n` embeddings of finite-dimensional boundaryless
manifolds into finite-dimensional Hausdorff second-countable smooth boundaryless manifolds, and let
`f : Q ≃ₘ^n⟮J, J'⟯ Q'` be a `C^n` diffeomorphism (`1 ≤ m ≤ ∞`, `m + 1 ≤ n`). Every `C^m` family
`A q : T_(i q) M ≃L[ℝ] T_(j (f q)) N` (in `inTangentCoordinates`) satisfying
`A q ∘ di_q = dj_(f q) ∘ df_q` is realized as the ambient differential along `Q` of a `C^m`
diffeomorphism `Φ : U ≃ₘ^m⟮I, I'⟯ V` between open subsets `U ⊆ O_M` and `V ⊆ O_N` sending `i q` to
`j (f q)`. -/
theorem exists_diffeomorph_opens_mfderiv_eq_subset
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    {i : Q → M} (hi : Manifold.IsSmoothEmbedding J I n i)
    {j : Q' → N} (hj : Manifold.IsSmoothEmbedding J' I' n j)
    (f : Q ≃ₘ^n⟮J, J'⟯ Q') (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i (fun q ↦ j (f q))
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
        mfderiv J' I' j (f q) ∘L mfderiv J J' f q)
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hjO : range j ⊆ O_N) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ^m⟮I, I'⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set N) ⊆ O_N ∧
      ∀ q : Q, ∃ hq : i q ∈ U, (Φ ⟨i q, hq⟩ : N) = j (f q) ∧
        mfderiv I I' (fun x : U ↦ (Φ x : N)) ⟨i q, hq⟩ =
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) := by
  have hn1 : 1 ≤ n := le_add_self.trans hm
  have hm_le_n : m ≤ n := le_self_add.trans hm
  let i_emb : TauCeti.SmoothEmbedding J I n Q M := ⟨⟨i, hi.contMDiff⟩, hi⟩
  have hg : ContMDiff J I' m (fun q ↦ j (f q)) :=
    (hj.contMDiff.comp f.contMDiff).of_le hm_le_n
  have hg_emb : IsEmbedding (fun q ↦ j (f q)) := hj.isEmbedding.comp f.toHomeomorph.isEmbedding
  have hgO : range (fun q ↦ j (f q)) ⊆ O_N := by
    rintro _ ⟨q, rfl⟩
    exact hjO (mem_range_self (f q))
  have hAi' (q : Q) :
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i_emb q =
        mfderiv J I' (fun q ↦ j (f q)) q := by
    have hchain : mfderiv J I' (j ∘ f) q = mfderiv J' I' j (f q) ∘L mfderiv J J' f q :=
      mfderiv_comp q (((hj.contMDiff.of_le hn1).contMDiffAt).mdifferentiableAt one_ne_zero)
        (((f.contMDiff.of_le hn1).contMDiffAt).mdifferentiableAt one_ne_zero)
    exact (hAi q).trans hchain.symm
  exact i_emb.exists_diffeomorph_opens_mfderiv_eq_subset hm hm1 hg hg_emb A hA hAi' hOM hiO hON hgO

/-- **Neighbourhood diffeomorphism with prescribed ambient derivative.** Specialization of
`exists_diffeomorph_opens_mfderiv_eq_subset` without ambient open-set constraints. -/
theorem exists_diffeomorph_opens_mfderiv_eq
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    {i : Q → M} (hi : Manifold.IsSmoothEmbedding J I n i)
    {j : Q' → N} (hj : Manifold.IsSmoothEmbedding J' I' n j)
    (f : Q ≃ₘ^n⟮J, J'⟯ Q') (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i (fun q ↦ j (f q))
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
        mfderiv J' I' j (f q) ∘L mfderiv J J' f q) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ^m⟮I, I'⟯ V),
      ∀ q : Q, ∃ hq : i q ∈ U, (Φ ⟨i q, hq⟩ : N) = j (f q) ∧
        mfderiv I I' (fun x : U ↦ (Φ x : N)) ⟨i q, hq⟩ =
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) := by
  obtain ⟨U, V, Φ, -, -, hΦ⟩ :=
    hi.exists_diffeomorph_opens_mfderiv_eq_subset hj f hm hm1 A hA hAi
      isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
  exact ⟨U, V, Φ, hΦ⟩

end Manifold.IsSmoothEmbedding

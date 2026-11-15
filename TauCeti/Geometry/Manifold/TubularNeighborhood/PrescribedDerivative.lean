/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Tubular neighbourhood diffeomorphisms with prescribed ambient derivative

Let `i : Q → M` be a smooth embedding of a boundaryless manifold into a Hausdorff second countable
boundaryless manifold, let `g : Q → N` be a smooth map into another Hausdorff second countable
boundaryless manifold which is a topological embedding, and let
`A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (g q)` be a smooth family of continuous
linear equivalences extending the differential along `Q` in the sense that
`A q ∘ di_q = dg_q` for every `q : Q` (where smoothness of `A` is smoothness of its coordinate
expressions `inTangentCoordinates`).

This file proves that `A` is realized as the ambient differential along `Q` of a diffeomorphism
`Φ : U ≃ₘ^m⟮I, I'⟯ V` between open neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_N` of
`range g`, sending `i q` to `g q`
(`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq_subset` and
`Manifold.IsSmoothEmbedding.exists_diffeomorph_opens_mfderiv_eq`). Neither compactness of `Q` nor
closedness of the embedded images is required.

## Method of proof

Choose auxiliary smooth Riemannian metrics on `M` and `N`. On the intrinsic normal bundle `ν` of
`i`, the Riemannian normal exponential of `i` gives a partial diffeomorphism `Φ₀` from an open
neighbourhood of the zero section onto an open subset of `O_M`, whose differential at `0_q` sends
`(u, v)` to `di_q u + r_q v`, where `r_q` is the orthogonal normal representative in `T_(i q) M`.

Transporting `r_q v` to `T_(g q) N` via `A q` and exponentiating in `N` defines the **twisted
normal exponential** `p ↦ exp^N_(g p.proj) (A p.proj (r_(p.proj) p.2))`
(`TauCeti.SmoothEmbedding.twistedNormalExp`). Its differential at `0_q` sends `(u, v)` to
`dg_q u + A q (r_q v)`; when `A q ∘ di_q = dg_q`, this equals `A q ∘ d(i.normalExp)_(0_q)`, which
is invertible. Since the restriction of the twisted normal exponential to the zero section is the
embedding `g`, `IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section` upgrades it to a
partial diffeomorphism `Φ₁` near the zero section with target in `O_N`. The composite
`Φ₀.symm.trans Φ₁` restricts to the desired diffeomorphism of open neighbourhoods.

Conversely, differentiating any diffeomorphism of open neighbourhoods extending `g` along `i`
produces a smooth family of ambient tangent equivalences in `inTangentCoordinates` extending `dg`
(`Diffeomorph.contMDiffAt_inTangentCoordinates_mfderiv_opens`,
`Diffeomorph.mfderiv_opens_comp_mfderiv`), and over finite-dimensional tangent fibres smoothness in
`inTangentCoordinates` is intrinsically characterized by sending smooth tangent lifts along the
source map to smooth tangent lifts along the target map
(`TauCeti.Manifold.contMDiffAt_inTangentCoordinates_iff`). When `A q` intertwines two differential
`k`-forms `σ` and `τ` at `i q` and `g q`, the pulled-back form `Φ^* (τ|_V)` agrees with `σ|_U` as a
full ambient `k`-form at every point of `i(Q)` (`TauCeti.SmoothForm.mpullback_eq_at_of_mfderiv_eq`).

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

/-- The natural open domain in the intrinsic normal bundle of `i` on which the orthogonal normal
representative, transported along `A` into `T_(g q) N`, lies in the Riemannian exponential domain
of `N`. -/
def twistedNormalExpDomain (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) :
    Set (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
  {p | A p.proj (i.normalRepresentative p.proj hn p.2) ∈ Manifold.expDomain I' N (g p.proj)}

/-- The **twisted normal exponential** of an embedding `i : Q → M` along a map `g : Q → N` and a
family `A q : T_(i q) M →L[ℝ] T_(g q) N`: it sends a normal class `(q, v)` to the Riemannian
exponential at `g q` of `A q` applied to the orthogonal representative of `v` in `T_(i q) M`. -/
def twistedNormalExp (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) : N :=
  Manifold.riemannianExp I' N (g p.proj) (A p.proj (i.normalRepresentative p.proj hn p.2))

/-- Membership in `twistedNormalExpDomain` unpacks to membership of the transported orthogonal
normal representative in `Manifold.expDomain`. -/
theorem mem_twistedNormalExpDomain (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) :
    p ∈ i.twistedNormalExpDomain (P := P) hn A ↔
      A p.proj (i.normalRepresentative p.proj hn p.2) ∈ Manifold.expDomain I' N (g p.proj) :=
  Iff.rfl

/-- Evaluating `twistedNormalExp` exponentiates the `A`-image of the orthogonal normal
representative at `g p.proj`. -/
theorem twistedNormalExp_apply (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))
    (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) :
    i.twistedNormalExp (P := P) hn A p =
      Manifold.riemannianExp I' N (g p.proj) (A p.proj (i.normalRepresentative p.proj hn p.2)) :=
  (rfl)

/-- Every point of the zero section of the normal bundle lies in `twistedNormalExpDomain`. -/
@[simp]
theorem zeroSection_mem_twistedNormalExpDomain
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0)
    {g : Q → N} (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) (q : Q) :
    zeroSection P (fun q ↦ i.NormalSpace q hn) q ∈ i.twistedNormalExpDomain (P := P) hn A := by
  simp [mem_twistedNormalExpDomain, zeroSection]

/-- On the zero section of the normal bundle, the twisted normal exponential agrees with `g`. -/
@[simp]
theorem twistedNormalExp_zeroSection [I'.Boundaryless] [T2Space N]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) {g : Q → N}
    (A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)) (q : Q) :
    i.twistedNormalExp (P := P) hn A (zeroSection P (fun q ↦ i.NormalSpace q hn) q) = g q := by
  simp [twistedNormalExp_apply, zeroSection, Manifold.riemannianExp_zero]

end TwistedNormalExpDefs

section TwistedNormalExp

variable {F E E' P K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace K] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace K Q]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {n m : ℕ∞ω}

/-- Transporting the orthogonal normal representative of `i` by a `C^m` family `A` (in
`inTangentCoordinates`) gives a `C^m` map from the intrinsic normal bundle of `i` into `TN`. -/
theorem contMDiff_twistedNormalRepresentative [ENat.LEInfty m] [IsManifold J (m + 1) Q]
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
  have hm' : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold I (m + 1) M := .of_le hm'
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x) :=
    .of_le ENat.LEInfty.out
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

variable [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y)]

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
  let := i.normalSpaceFiberBundle hn hdim
  have hcont := (i.contMDiff_twistedNormalRepresentative (m := 0) hn
    (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim hg hA).continuous
  convert (Manifold.isOpen_setOfPred_mem_expDomain (I := I') (M := N)).preimage hcont using 1
  ext p
  exact i.mem_twistedNormalExpDomain hn A p

/-- The twisted normal exponential is `C^m` on its natural open domain for a `C^n` embedding `i`
with `m + 1 ≤ n` and `C^m` data `g, A`. -/
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
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  convert ((Manifold.contMDiffOn_riemannianExp_tangentBundle (I := I') (M := N)).of_le
    ENat.LEInfty.out).comp
    (i.contMDiff_twistedNormalRepresentative hn hm hdim hg hA).contMDiffOn
    (fun p hp ↦ (i.mem_twistedNormalExpDomain hn A p).mp hp) using 1
  funext p
  exact i.twistedNormalExp_apply hn A p

/-- Under the canonical splitting of the tangent space along the zero section of the normal bundle
of `i`, the differential of `twistedNormalExp` sends `(u, v)` to
`dg_q u + A q (i.normalRepresentative q hn v)`. -/
theorem mfderiv_twistedNormalExp_zeroSection_apply [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g A q₀) q₀)
    (q : Q) (u : TangentSpace J q) (v : i.NormalSpace q hn) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    mfderiv (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q)
        ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
      mfderiv J I' g q u + A q (i.normalRepresentative q hn v) := by
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
  have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold I' (1 + 1) N := .of_le (n := ∞) (by norm_cast)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle (m := 1) hn (h2m.trans hm) hdim
  have hopen := i.isOpen_twistedNormalExpDomain hn hdim (hg.of_le zero_le)
    (fun q₀ ↦ (hA q₀).of_le zero_le)
  have he : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :=
    (((i.contMDiffOn_twistedNormalExp hn hm hdim hg hA).of_le hm1).contMDiffAt
      (hopen.mem_nhds (i.zeroSection_mem_twistedNormalExpDomain hn A q))).mdifferentiableAt
      one_ne_zero
  rw [Bundle.zeroSectionTangentEquiv_symm_eq, map_add]
  congr 1
  · have h := mfderiv_comp_apply q he (mdifferentiableAt_zeroSection ℝ _) u
    have hfun : i.twistedNormalExp (P := P) hn A ∘
        zeroSection P (fun q ↦ i.NormalSpace q hn) = g :=
      funext (i.twistedNormalExp_zeroSection hn A)
    rw [hfun] at h
    exact h.symm
  · rw [Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → TotalSpace P (fun q ↦ i.NormalSpace q hn) := fun t ↦ ⟨q, t • v⟩
    have hl : ContMDiff 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, v⟩ :
        TotalSpace P (fun q ↦ i.NormalSpace q hn))))
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) he
      (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    let w : TangentSpace I' (g q) := A q (i.normalRepresentative q hn v)
    have hfun : i.twistedNormalExp (P := P) hn A ∘ line =
        Manifold.riemannianExp I' N (g q) ∘ (fun t : ℝ ↦ t • w) := by
      funext t
      simp only [Function.comp_apply, line, twistedNormalExp_apply, map_smul, w]
    rw [hfun] at h
    have hexp₀ := Manifold.hasMFDerivAt_riemannianExp_zero (I := I') (g q)
    have hvec : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace I' (g q))
        (fun t : ℝ ↦ t • w) 0 (ContinuousLinearMap.toSpanSingleton ℝ w) :=
      (ContinuousLinearMap.toSpanSingleton ℝ w).hasMFDerivAt
    have hc := mfderiv_comp_apply_of_eq (0 : ℝ) hexp₀.mdifferentiableAt
      hvec.mdifferentiableAt (by simp) (1 : ℝ)
    have hc₁ := Manifold.mfderiv_riemannianExp_apply_zero (I := I') (g q)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace I' (g q)) (fun t : ℝ ↦ t • w) (0 : ℝ) (1 : ℝ))
    have hc₂ : (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace I' (g q)) (fun t : ℝ ↦ t • w) (0 : ℝ) (1 : ℝ) :
        TangentSpace I' (g q)) = ContinuousLinearMap.toSpanSingleton ℝ w (1 : ℝ) :=
      DFunLike.congr_fun hvec.mfderiv (1 : ℝ)
    have hone := ContinuousLinearMap.toSpanSingleton_apply_one (M₁ := TangentSpace I' (g q)) ℝ w
    exact h.symm.trans (hc.trans (hc₁.trans (hc₂.trans hone)))

/-- When `A q ∘L mfderiv J I i q = mfderiv J I' g q`, the differential of `twistedNormalExp` at
`0_q` factors as `A q` composed with the differential of `i.normalExp` at `0_q`. -/
theorem mfderiv_twistedNormalExp_zeroSection_eq_comp [I.Boundaryless] [T2Space M]
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ F)
    {g : Q → N} (hg : ContMDiff J I' m g)
    {A : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q)}
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' i g A q₀) q₀)
    {q : Q} (hAq : A q ∘L mfderiv J I i q = mfderiv J I' g q) :
    haveI : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    (mfderiv (J.prod 𝓘(ℝ, P)) I' (i.twistedNormalExp (P := P) hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :
          TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
            TangentSpace I' (g q)) =
      A q ∘L (mfderiv (J.prod 𝓘(ℝ, P)) I (i.normalExp (P := P) hn)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :
          TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
            TangentSpace I (i q)) := by
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
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
    i.mfderiv_twistedNormalExp_zeroSection_apply hn hm hm1 hdim hg hA q u v
  have hD₀ (u : TangentSpace J q) (v : i.NormalSpace q hn) :
      D₀ ((Bundle.zeroSectionTangentEquiv (I := J) q).symm (u, v)) =
        mfderiv J I i q u + i.normalRepresentative q hn v :=
    i.mfderiv_normalExp_zeroSection_apply hn (h2m.trans hm) hdim q u v
  ext w
  obtain ⟨⟨u, v⟩, rfl⟩ :=
    (Bundle.zeroSectionTangentEquiv (I := J) (F := P)
      (V := fun q ↦ i.NormalSpace q hn) q).symm.surjective w
  have hAq_u : A q (mfderiv J I i q u) = mfderiv J I' g q u := DFunLike.congr_fun hAq u
  exact (hD₁ u v).trans <|
    (congrArg (· + A q (i.normalRepresentative q hn v)) hAq_u.symm).trans <|
      (map_add (A q) _ _).symm.trans (congrArg (A q) (hD₀ u v).symm)

/-- When `A q` is invertible and `A q ∘L mfderiv J I i q = mfderiv J I' g q`, the twisted normal
exponential is a `C^m` local diffeomorphism at `0_q`. -/
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
  have : IsManifold I' (m + 1) N := .of_le (n := ∞) hminfty
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle hn hm hdim
  obtain ⟨e₀, he₀⟩ := i.isInvertible_mfderiv_normalExp_zeroSection hn (h2m.trans hm) hdim q
  have hcomp := i.mfderiv_twistedNormalExp_zeroSection_eq_comp hn hm hm1 hdim hg hA hAq
  have heq : ((e₀.trans (A q) :
      TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) ≃L[ℝ]
        TangentSpace I' (g q)) :
      TangentSpace (J.prod 𝓘(ℝ, P)) (zeroSection P (fun q ↦ i.NormalSpace q hn) q) →L[ℝ]
        TangentSpace I' (g q)) =
      mfderiv (J.prod 𝓘(ℝ, P)) I'
        (i.twistedNormalExp (P := P) hn
          (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q))))
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) := by
    ext w
    exact (congrArg (A q) (DFunLike.congr_fun he₀ w)).trans (DFunLike.congr_fun hcomp.symm w)
  exact isLocalDiffeomorphAt_of_mfderiv_eq
    (i.contMDiffOn_twistedNormalExp hn hm hdim hg hA)
    (i.isOpen_twistedNormalExpDomain hn hdim (hg.of_le zero_le) (fun q₀ ↦ (hA q₀).of_le zero_le))
    (i.zeroSection_mem_twistedNormalExpDomain hn _ q)
    BoundarylessManifold.isInteriorPoint hm1 heq

/-- When `g` is a topological embedding, the twisted normal exponential restricts to a single `C^m`
partial diffeomorphism on an open neighbourhood of the zero section with target inside any
prescribed open neighbourhood `O` of `range g`. -/
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
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : T2Space Q := hg_emb.t2Space
  have : SecondCountableTopology Q := hg_emb.isInducing.secondCountableTopology
  have : LocallyCompactSpace H' := I'.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  have : LocallyCompactSpace (ModelProd K P) := (J.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
    ChartedSpace.locallyCompactSpace (ModelProd K P) _
  have : MetrizableSpace N := Manifold.metrizableSpace I' N
  have : MetrizableSpace (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
    Manifold.metrizableSpace (J.prod 𝓘(ℝ, P)) _
  have : Nonempty (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
    Nonempty.map (zeroSection P (fun q ↦ i.NormalSpace q hn)) inferInstance
  let A_clm : ∀ q : Q, TangentSpace I (i q) →L[ℝ] TangentSpace I' (g q) := fun q ↦ A q
  let Ψ := i.twistedNormalExp (P := P) hn A_clm
  let U := {p | IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I' m Ψ p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp ↦ hp.eventually
  have hopen := i.isOpen_twistedNormalExpDomain hn hdim (hg.of_le zero_le)
    (fun q₀ ↦ (hA q₀).of_le zero_le)
  let S := (U ∩ i.twistedNormalExpDomain (P := P) hn A_clm) ∩ Ψ ⁻¹' O
  have hS : IsOpen S :=
    ContinuousOn.isOpen_inter_preimage
      ((i.contMDiffOn_twistedNormalExp hn hm hdim hg hA).continuousOn.mono inter_subset_right)
      (hU.inter hopen) hO
  have hzero : range (zeroSection P (fun q ↦ i.NormalSpace q hn)) ⊆ S := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨i.isLocalDiffeomorphAt_twistedNormalExp_zeroSection hn hm hm1 hdim hg A hA (hAi q),
      i.zeroSection_mem_twistedNormalExpDomain hn A_clm q⟩,
      show i.twistedNormalExp (P := P) hn A_clm (zeroSection P (fun q ↦ i.NormalSpace q hn) q) ∈ O
        by rw [i.twistedNormalExp_zeroSection]; exact hgO (mem_range_self q)⟩
  have hlocal : IsLocalDiffeomorphOn (J.prod 𝓘(ℝ, P)) I' m Ψ S := fun p ↦ p.property.1.1
  have hcore : Ψ ∘ zeroSection P (fun q ↦ i.NormalSpace q hn) = g :=
    funext (i.twistedNormalExp_zeroSection hn A_clm)
  obtain ⟨Φ, hzeroΦ, hΦS, htarget, hΦ⟩ := hlocal.exists_partialDiffeomorph_near_section
    hS hzero (_root_.Bundle.Trivialization.continuous_zeroSection ℝ)
    (π P (fun q ↦ i.NormalSpace q hn))
    (FiberBundle.continuous_proj _ _) (fun _ ↦ rfl) (hcore ▸ hg_emb.isInducing)
  refine ⟨Φ, fun q ↦ hzeroΦ (mem_range_self q), fun p hp ↦ (hΦS hp).1.2, ?_, hΦ⟩
  rw [htarget]
  rintro _ ⟨p, hp, rfl⟩
  exact (hΦS hp).2

end TwistedNormalExp

section PrescribedDerivative

variable {F E E' K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
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
`i : Q → M` of a nonempty boundaryless manifold, a `C^m` topological embedding `g : Q → N`
(`1 ≤ m`, `m + 1 ≤ n`), and a `C^m` family of continuous linear equivalences
`A q : T_(i q) M ≃L[ℝ] T_(g q) N` in `inTangentCoordinates` satisfying `A q ∘ di_q = dg_q`, there
exists a `C^m` partial diffeomorphism `Ψ` from `M` to `N` whose source lies in `O_M` and contains
`range i`, whose target lies in `O_N`, and which satisfies `Ψ (i q) = g q` and `dΨ_(i q) = A q`
for every `q : Q`. -/
theorem exists_partialDiffeomorph_mfderiv_eq_subset [Nonempty Q]
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
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
  have h2m : (1 : ℕ∞ω) + 1 ≤ m + 1 := by gcongr
  have : IsManifold J 1 Q := .of_le (n := m + 1) le_add_self
  have : IsManifold J (1 + 1) Q := .of_le (n := m + 1) h2m
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
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
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle (m := 1) hn (h2m.trans hm) hdim
  obtain ⟨Φ₀, hzero₀, -, htarget₀, -, hΦ₀⟩ :=
    i.exists_partialDiffeomorph_normalExp_subset (P := P) (m := m) hn hm hm1 hdim hOM hiO
  obtain ⟨Φ₁, hzero₁, -, htarget₁, hΦ₁⟩ :=
    i.exists_partialDiffeomorph_twistedNormalExp_subset (P := P) (m := m)
      hn hm hm1 hdim hg hg_emb A hA hAi hON hgO
  let Ψ := Φ₀.symm.trans Φ₁
  refine ⟨Ψ, ?_, ?_, fun q ↦ ?_⟩
  · intro x hx
    exact htarget₀ hx.1
  · intro y hy
    exact htarget₁ hy.1
  · let z₀ := zeroSection P (fun q ↦ i.NormalSpace q hn) q
    have hΦ₀z : Φ₀ z₀ = i q := by rw [hΦ₀, i.normalExp_zeroSection]
    have hΦ₁z : Φ₁ z₀ = g q := by rw [hΦ₁, i.twistedNormalExp_zeroSection]
    have hiq_t : i q ∈ Φ₀.target := hΦ₀z ▸ Φ₀.map_source (hzero₀ q)
    have hsymm_iq : Φ₀.symm (i q) = z₀ := by
      rw [← hΦ₀z]
      exact Φ₀.left_inv (hzero₀ q)
    have hiq_src : i q ∈ Ψ.source := by
      rw [PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage, hsymm_iq]
      exact ⟨hiq_t, hzero₁ q⟩
    have hΨ_iq : Ψ (i q) = g q := by
      rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hsymm_iq, hΦ₁z]
    refine ⟨hiq_src, hΨ_iq, ?_⟩
    -- Near `z₀`, `Φ₀` and `Φ₁` agree with `i.normalExp` and `i.twistedNormalExp`, and
    -- `Φ₀ ∘ Φ₀.symm = id` near `i q`, so the chain rule identifies `dΨ_(i q)` with `A q`.
    have md₀ : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I Φ₀ z₀ :=
      ((Φ₀.contMDiffOn.of_le hm1).contMDiffAt
        (Φ₀.open_source.mem_nhds (hzero₀ q))).mdifferentiableAt one_ne_zero
    have md₀_symm : MDifferentiableAt I (J.prod 𝓘(ℝ, P)) Φ₀.symm (i q) :=
      ((Φ₀.symm.contMDiffOn.of_le hm1).contMDiffAt
        (Φ₀.open_target.mem_nhds hiq_t)).mdifferentiableAt one_ne_zero
    have md₁ : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I' Φ₁ z₀ :=
      ((Φ₁.contMDiffOn.of_le hm1).contMDiffAt
        (Φ₁.open_source.mem_nhds (hzero₁ q))).mdifferentiableAt one_ne_zero
    have hright : (Φ₀ ∘ Φ₀.symm) =ᶠ[𝓝 (i q)] (_root_.id : M → M) := by
      filter_upwards [Φ₀.open_target.mem_nhds hiq_t] with x hx
      exact Φ₀.right_inv hx
    have h_eq₁ {z} (hz : z = z₀) (u : F × P) :
        (mfderiv (J.prod 𝓘(ℝ, P)) I' Φ₁ z u : E') =
          (mfderiv (J.prod 𝓘(ℝ, P)) I' Φ₁ z₀ u : E') := by
      subst hz; rfl
    have h_eq₀ {z} (hz : z = z₀) (u : F × P) :
        (mfderiv (J.prod 𝓘(ℝ, P)) I Φ₀ z u : E) =
          (mfderiv (J.prod 𝓘(ℝ, P)) I Φ₀ z₀ u : E) := by
      subst hz; rfl
    have h_fn₁ {f₁ f₂ : TotalSpace P (fun q ↦ i.NormalSpace q hn) → N} (hf : f₁ = f₂)
        (u : F × P) :
        (mfderiv (J.prod 𝓘(ℝ, P)) I' f₁ z₀ u : E') =
          (mfderiv (J.prod 𝓘(ℝ, P)) I' f₂ z₀ u : E') := by
      subst hf; rfl
    have h_fn₀ {f₁ f₂ : TotalSpace P (fun q ↦ i.NormalSpace q hn) → M} (hf : f₁ = f₂)
        (u : F × P) :
        (mfderiv (J.prod 𝓘(ℝ, P)) I f₁ z₀ u : E) =
          (mfderiv (J.prod 𝓘(ℝ, P)) I f₂ z₀ u : E) := by
      subst hf; rfl
    have h_coe {f : M → N} (hf : f = Φ₁ ∘ Φ₀.symm) (v : TangentSpace I (i q)) :
        (mfderiv I I' f (i q) v : E') =
          (mfderiv I I' (Φ₁ ∘ Φ₀.symm) (i q) v : E') := by
      subst hf; rfl
    have hcomp_exp :=
      i.mfderiv_twistedNormalExp_zeroSection_eq_comp hn hm hm1 hdim hg hA (hAi q)
    ext v
    let w : F × P := mfderiv I (J.prod 𝓘(ℝ, P)) Φ₀.symm (i q) v
    have h₀w : (mfderiv (J.prod 𝓘(ℝ, P)) I (i.normalExp (P := P) hn) z₀ w :
        TangentSpace I (i q)) = v :=
      (h_fn₀ hΦ₀ w).symm.trans <| (h_eq₀ hsymm_iq w).symm.trans <|
        (DFunLike.congr_fun (mfderiv_comp_of_eq (x := i q) md₀ md₀_symm hsymm_iq).symm v).trans <|
          DFunLike.congr_fun
            ((hright.mfderiv_eq (I := I) (I' := I)).trans (mfderiv_id (I := I))) v
    exact (h_coe (PartialDiffeomorph.coe_trans Φ₀.symm Φ₁) v).trans <|
      (DFunLike.congr_fun (mfderiv_comp_of_eq (x := i q) md₁ md₀_symm hsymm_iq) v).trans <|
        (h_eq₁ hsymm_iq w).trans <| (h_fn₁ hΦ₁ w).trans <|
          (DFunLike.congr_fun hcomp_exp w).trans (congrArg (A q) h₀w)

/-- **Tubular neighbourhood diffeomorphism with prescribed ambient derivative.** Given a `C^n`
embedding `i : Q → M` of a boundaryless manifold, a `C^m` topological embedding `g : Q → N`
(`1 ≤ m`, `m + 1 ≤ n`), and a `C^m` family of continuous linear equivalences
`A q : T_(i q) M ≃L[ℝ] T_(g q) N` in `inTangentCoordinates` satisfying `A q ∘ di_q = dg_q`, there
exist open neighbourhoods `U ⊆ O_M` of `range i` and `V ⊆ O_N` of `range g` and a `C^m`
diffeomorphism `Φ : U ≃ₘ^m⟮I, I'⟯ V` sending `i q` to `g q` with ambient differential `A q` at
`i q` for every `q : Q`. Neither compactness nor nonemptiness of `Q` is required. -/
theorem exists_diffeomorph_opens_mfderiv_eq_subset
    [ENat.LEInfty m] [IsManifold J (m + 1) Q]
    (i : SmoothEmbedding J I n Q M) (hn : n ≠ 0) (hm : m + 1 ≤ n) (hm1 : 1 ≤ m)
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
    let U : Opens M := ⊥
    let V : Opens N := ⊥
    have : IsEmpty U := ⟨fun x ↦ x.2⟩
    have : IsEmpty V := ⟨fun y ↦ y.2⟩
    let Φ : U ≃ₘ^m⟮I, I'⟯ V :=
      { Equiv.equivOfIsEmpty U V with
        contMDiff_toFun := fun x ↦ (IsEmpty.false x).elim
        contMDiff_invFun := fun y ↦ (IsEmpty.false y).elim }
    exact ⟨U, V, Φ, empty_subset O_M, empty_subset O_N, fun q ↦ (hQ.false q).elim⟩
  | inr hQ =>
    obtain ⟨Ψ, hsrc, htgt, hΨ⟩ :=
      i.exists_partialDiffeomorph_mfderiv_eq_subset hn hm hm1 hg hg_emb A hA hAi hOM hiO hON hgO
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
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace K] [TopologicalSpace K'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F K} {J' : ModelWithCorners ℝ F' K'}
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [J.Boundaryless] [I.Boundaryless] [I'.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace K Q] [IsManifold J ∞ Q]
  [TopologicalSpace Q'] [ChartedSpace K' Q'] [IsManifold J' ∞ Q']
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] [T2Space N]
  [SecondCountableTopology N]

/-- **Smooth neighbourhood diffeomorphism with prescribed ambient derivative, inside prescribed
open sets.** Let `i : Q → M` and `j : Q' → N` be smooth embeddings of boundaryless manifolds into
Hausdorff second countable boundaryless manifolds, and `f : Q ≃ₘ⟮J, J'⟯ Q'` a diffeomorphism.
Every smooth family `A q : T_(i q) M ≃L[ℝ] T_(j (f q)) N` (smooth in `inTangentCoordinates`)
satisfying `A q ∘ di_q = dj_(f q) ∘ df_q` is realized as the ambient differential along `Q` of a
smooth diffeomorphism `Φ : U ≃ₘ⟮I, I'⟯ V` between open subsets `U ⊆ O_M` and `V ⊆ O_N` sending
`i q` to `j (f q)`. -/
theorem exists_diffeomorph_opens_mfderiv_eq_subset
    {i : Q → M} (hi : Manifold.IsSmoothEmbedding J I ∞ i)
    {j : Q' → N} (hj : Manifold.IsSmoothEmbedding J' I' ∞ j)
    (f : Q ≃ₘ⟮J, J'⟯ Q')
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I I' i (fun q ↦ j (f q))
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
        mfderiv J' I' j (f q) ∘L mfderiv J J' f q)
    {O_M : Set M} (hOM : IsOpen O_M) (hiO : range i ⊆ O_M)
    {O_N : Set N} (hON : IsOpen O_N) (hjO : range j ⊆ O_N) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ⟮I, I'⟯ V),
      (U : Set M) ⊆ O_M ∧ (V : Set N) ⊆ O_N ∧
      ∀ q : Q, ∃ hq : i q ∈ U, (Φ ⟨i q, hq⟩ : N) = j (f q) ∧
        mfderiv I I' (fun x : U ↦ (Φ x : N)) ⟨i q, hq⟩ =
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) := by
  have : IsManifold J (∞ + 1) Q := by simpa using (inferInstance : IsManifold J ∞ Q)
  have : IsManifold J 1 Q := IsManifold.of_le (I := J) (n := ∞) (by simp)
  have : IsManifold J' 1 Q' := IsManifold.of_le (I := J') (n := ∞) (by simp)
  have : IsManifold I' 1 N := IsManifold.of_le (I := I') (n := ∞) (by simp)
  let i_emb : TauCeti.SmoothEmbedding J I ∞ Q M := ⟨⟨i, hi.contMDiff⟩, hi⟩
  have hg : ContMDiff J I' ∞ (fun q ↦ j (f q)) := hj.contMDiff.comp f.contMDiff
  have hg_emb : IsEmbedding (fun q ↦ j (f q)) := hj.isEmbedding.comp f.toHomeomorph.isEmbedding
  have hgO : range (fun q ↦ j (f q)) ⊆ O_N := by
    rintro _ ⟨q, rfl⟩
    exact hjO (mem_range_self (f q))
  have hAi' (q : Q) :
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i_emb q =
        mfderiv J I' (fun q ↦ j (f q)) q := by
    have hchain : mfderiv J I' (j ∘ f) q = mfderiv J' I' j (f q) ∘L mfderiv J J' f q :=
      mfderiv_comp q (hj.contMDiff.mdifferentiableAt (by simp))
        (f.contMDiff.mdifferentiableAt (by simp))
    exact (hAi q).trans hchain.symm
  exact i_emb.exists_diffeomorph_opens_mfderiv_eq_subset (m := ∞) (by simp) (by simp) (by simp)
    hg hg_emb A hA hAi' hOM hiO hON hgO

/-- **Smooth neighbourhood diffeomorphism with prescribed ambient derivative.** Specialization of
`exists_diffeomorph_opens_mfderiv_eq_subset` without ambient open-set constraints. -/
theorem exists_diffeomorph_opens_mfderiv_eq
    {i : Q → M} (hi : Manifold.IsSmoothEmbedding J I ∞ i)
    {j : Q' → N} (hj : Manifold.IsSmoothEmbedding J' I' ∞ j)
    (f : Q ≃ₘ⟮J, J'⟯ Q')
    (A : ∀ q : Q, TangentSpace I (i q) ≃L[ℝ] TangentSpace I' (j (f q)))
    (hA : ∀ q₀ : Q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I I' i (fun q ↦ j (f q))
        (fun q ↦ (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q)))) q₀) q₀)
    (hAi : ∀ q : Q,
      (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) ∘L mfderiv J I i q =
        mfderiv J' I' j (f q) ∘L mfderiv J J' f q) :
    ∃ (U : Opens M) (V : Opens N) (Φ : U ≃ₘ⟮I, I'⟯ V),
      ∀ q : Q, ∃ hq : i q ∈ U, (Φ ⟨i q, hq⟩ : N) = j (f q) ∧
        mfderiv I I' (fun x : U ↦ (Φ x : N)) ⟨i q, hq⟩ =
          (A q : TangentSpace I (i q) →L[ℝ] TangentSpace I' (j (f q))) := by
  obtain ⟨U, V, Φ, -, -, hΦ⟩ :=
    hi.exists_diffeomorph_opens_mfderiv_eq_subset hj f A hA hAi
      isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
  exact ⟨U, V, Φ, hΦ⟩

end Manifold.IsSmoothEmbedding

section ConverseAndPullback

variable {F E E' K H H' Q M N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace Q] [ChartedSpace K Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

namespace Diffeomorph

/-- **Converse regularity in `inTangentCoordinates`.** If `Φ : U ≃ₘ^n⟮I, I'⟯ V` is a `C^n`
diffeomorphism of open subsets and `iU : Q → U` is `C^m` with `m + 1 ≤ n`, then the ambient
differentials `q ↦ mfderiv I I' (Subtype.val ∘ Φ) (iU q)` along `i := Subtype.val ∘ iU` and
`g := Subtype.val ∘ Φ ∘ iU` depend `C^m`-smoothly on `q` in `inTangentCoordinates`. -/
theorem contMDiffAt_inTangentCoordinates_mfderiv_opens [IsManifold J 1 Q] {m n : ℕ∞ω}
    {U : Opens M} {V : Opens N} (Φ : U ≃ₘ^n⟮I, I'⟯ V) {iU : Q → U} (hiU : ContMDiff J I m iU)
    (hmn : m + 1 ≤ n) (q₀ : Q) :
    ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m
      (inTangentCoordinates I I' (fun q ↦ (iU q : M)) (fun q ↦ (Φ (iU q) : N))
        (fun q ↦ (mfderiv I I' (fun x : U ↦ (Φ x : N)) (iU q) :
          TangentSpace I (iU q : M) →L[ℝ] TangentSpace I' (Φ (iU q) : N))) q₀) q₀ := by
  have hΦval : ContMDiffAt (J.prod I) I' n (Function.uncurry fun _ : Q ↦ fun x : U ↦ (Φ x : N))
      (q₀, iU q₀) :=
    ((contMDiff_subtype_val.comp Φ.contMDiff).contMDiffAt).comp (q₀, iU q₀) contMDiffAt_snd
  have hU := hΦval.mfderiv (fun _ : Q ↦ fun x : U ↦ (Φ x : N)) iU (hiU q₀) hmn
  refine hU.congr_of_eventuallyEq ?_
  filter_upwards [(hiU q₀).continuousAt.eventually
      (TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I)
        (iU q₀))]
    with q hsymm
  ext v
  let dΦM : TangentSpace I (iU q : M) →L[ℝ] TangentSpace I' (Φ (iU q) : N) :=
    mfderiv I I' (fun x : U ↦ (Φ x : N)) (iU q)
  let dΦU : TangentSpace I (iU q) →L[ℝ] TangentSpace I' (Φ (iU q) : N) :=
    mfderiv I I' (fun x : U ↦ (Φ x : N)) (iU q)
  let wU : TangentSpace I (iU q) :=
    (trivializationAt E (TangentSpace I : U → Type _) (iU q₀)).symmL ℝ (iU q) v
  let wM : TangentSpace I (iU q : M) :=
    (trivializationAt E (TangentSpace I : M → Type _) (iU q₀ : M)).symmL ℝ (iU q : M) v
  have hd : dΦM wM = dΦU wU :=
    (congrArg dΦM
      ((hsymm v).symm.trans
        (TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := I) (iU q) wU))).trans
      (rfl : dΦM wU = dΦU wU)
  exact congrArg
    ((trivializationAt E' (TangentSpace I') (Φ (iU q₀) : N)).continuousLinearMapAt ℝ
      (Φ (iU q) : N)) hd

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- **Converse tangent compatibility.** If `Φ : U ≃ₘ^n⟮I, I'⟯ V` (`1 ≤ n`) is a diffeomorphism of
open subsets and `iU : Q → U` is differentiable at `q`, then the ambient differential of `Φ` at
`iU q` intertwines the differentials of `i := Subtype.val ∘ iU` and `g := Subtype.val ∘ Φ ∘ iU`. -/
theorem mfderiv_opens_comp_mfderiv {n : ℕ∞ω} (hn : 1 ≤ n) {U : Opens M} {V : Opens N}
    (Φ : U ≃ₘ^n⟮I, I'⟯ V) {iU : Q → U} {q : Q} (hiU : MDifferentiableAt J I iU q) :
    (mfderiv I I' (fun x : U ↦ (Φ x : N)) (iU q) :
        TangentSpace I (iU q : M) →L[ℝ] TangentSpace I' (Φ (iU q) : N)) ∘L
      mfderiv J I (fun q ↦ (iU q : M)) q =
    mfderiv J I' (fun q ↦ (Φ (iU q) : N)) q := by
  ext u
  have hΦ : MDifferentiableAt I I' (fun x : U ↦ (Φ x : N)) (iU q) :=
    (((contMDiff_subtype_val.comp Φ.contMDiff).of_le hn).contMDiffAt).mdifferentiableAt one_ne_zero
  have hval := TauCeti.Manifold.mfderiv_subtype_val_comp_apply (I := I) (J := J) (f := iU) u
  have hchain := mfderiv_comp_apply q hΦ hiU u
  exact (congrArg (mfderiv I I' (fun x : U ↦ (Φ x : N)) (iU q)) hval).trans hchain.symm

end Diffeomorph

namespace TauCeti.SmoothForm

/-- **Ambient differential-form agreement along a submanifold.** Let `Φ : U ≃ₘ⟮I, I'⟯ V` be a
smooth diffeomorphism between open subsets of `M` and `N`. If at `x : U` we have `(Φ x : N) = y`,
`mfderiv I I' (Subtype.val ∘ Φ) x = A`, and `(τ.1 y).compContinuousLinearMap A = σ.1 x.1` for
smooth `k`-forms `σ` on `M` and `τ` on `N`, then `Φ^* (τ|_V)` and `σ|_U` agree as full ambient
`k`-forms at `x`. -/
theorem mpullback_eq_at_of_mfderiv_eq [IsManifold I ∞ M] [IsManifold I' ∞ N]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
    {U : Opens M} {V : Opens N} (Φ : U ≃ₘ⟮I, I'⟯ V)
    (σ : SmoothForm I M G k) (τ : SmoothForm I' N G k)
    {x : U} {y : N} (hxy : (Φ x : N) = y)
    {A : TangentSpace I (x : M) →L[ℝ] TangentSpace I' y}
    (hA : mfderiv I I' (fun z : U ↦ (Φ z : N)) x = A)
    (hform : (τ.1 y).compContinuousLinearMap A = σ.1 (x : M)) :
    (mpullback Φ Φ.contMDiff
        (mpullback (Subtype.val : V → N) contMDiff_subtype_val τ)).1 x =
      (mpullback (Subtype.val : U → M) contMDiff_subtype_val σ).1 x := by
  subst hxy
  ext v
  simp only [mpullback_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply]
  have hv (j : Fin k) :
      (mfderiv I I' Φ x (v j) : TangentSpace I' (Φ x : N)) = A (v j) :=
    (Manifold.mfderiv_subtype_val_comp_apply (I := I') (J := I) (f := Φ) (v j)).symm.trans
      (DFunLike.congr_fun hA (v j))
  calc
    τ.1 (Φ x : N) (fun j ↦ (mfderiv I I' Φ x (v j) : TangentSpace I' (Φ x : N)))
      = τ.1 (Φ x : N) (fun j ↦ A (v j)) := congrArg (τ.1 (Φ x : N)) (funext hv)
    _ = ((τ.1 (Φ x : N)).compContinuousLinearMap A) v := rfl
    _ = σ.1 (x : M) v := by rw [hform]

end TauCeti.SmoothForm

namespace TauCeti.Manifold

/-- **Intrinsic characterization of smoothness in `inTangentCoordinates`.** Over a
finite-dimensional tangent model `E`, a family of continuous linear maps
`ϕ q : T_(f q) M →L[ℝ] T_(g q) N` along `C^m` maps `f : Q → M` and `g : Q → N` is `C^m` at `q₀` in
`inTangentCoordinates` if and only if it sends every `C^m` tangent lift along `f` near `q₀` to a
`C^m` tangent lift along `g` near `q₀`. -/
theorem contMDiffAt_inTangentCoordinates_iff [FiniteDimensional ℝ E] {m : ℕ∞ω}
    {f : Q → M} {g : Q → N} {q₀ : Q}
    (hf : ContMDiffAt J I m f q₀) (hg : ContMDiffAt J I' m g q₀)
    (ϕ : ∀ q : Q, TangentSpace I (f q) →L[ℝ] TangentSpace I' (g q)) :
    ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E') m (inTangentCoordinates I I' f g ϕ q₀) q₀ ↔
      ∀ s : ∀ q : Q, TangentSpace I (f q),
        ContMDiffAt J (I.prod 𝓘(ℝ, E)) m (fun q ↦ TotalSpace.mk' E (f q) (s q)) q₀ →
        ContMDiffAt J (I'.prod 𝓘(ℝ, E')) m (fun q ↦ TotalSpace.mk' E' (g q) (ϕ q (s q))) q₀ := by
  refine ⟨fun hϕ _ hs ↦ hϕ.clm_apply_of_inCoordinates hs hg, fun h ↦ ?_⟩
  rw [TauCeti.contMDiffAt_clm_apply]
  intro v
  let s : ∀ q : Q, TangentSpace I (f q) :=
    fun q ↦ (trivializationAt E (TangentSpace I) (f q₀)).symmL ℝ (f q) v
  have hs : ContMDiffAt J (I.prod 𝓘(ℝ, E)) m (fun q ↦ TotalSpace.mk' E (f q) (s q)) q₀ := by
    rw [contMDiffAt_totalSpace_iff]
    refine ⟨hf, (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_⟩
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (f q₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (f q₀)))] with q hq
    -- Read the fibre coordinate of `⟨f q, s q⟩` in the preferred trivialization at `f q₀`.
    change (trivializationAt E (TangentSpace I) (f q₀) ⟨f q, s q⟩).2 = v
    dsimp only [s]
    rw [(trivializationAt E (TangentSpace I) (f q₀)).symmL_apply hq]
    exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) (f q₀)).apply_mk_symm hq v)
  have hϕs := (contMDiffAt_totalSpace_iff.1 (h s hs)).2
  refine hϕs.congr_of_eventuallyEq ?_
  filter_upwards [hg.continuousAt.preimage_mem_nhds
    ((trivializationAt E' (TangentSpace I') (g q₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E' (TangentSpace I') (g q₀)))] with q hq
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt E' (TangentSpace I') (g q₀)) hq (ϕ q (s q))

end TauCeti.Manifold

end ConverseAndPullback

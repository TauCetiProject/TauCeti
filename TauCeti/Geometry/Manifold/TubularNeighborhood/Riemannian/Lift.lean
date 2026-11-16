/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Topology.FiberBundle.Countable
import TauCeti.Topology.FiberBundle.Separation

/-!
# Riemannian exponential of a fibrewise linear bundle lift

Given a family of modules `V : Q → Type*` over `Q`, a map `g : Q → N` into a finite-dimensional
Riemannian manifold `N`, and a fibrewise continuous linear map
`L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)`, the **lifted Riemannian exponential**
`TauCeti.Bundle.liftExp g L` sends `(q, v) : TotalSpace P V` to `exp^N_(g q) (L q v)` on its
natural domain `TauCeti.Bundle.liftExpDomain g L`.

When the bundle lift `p ↦ (g p.proj, L p.proj p.2) : TotalSpace P V → TangentBundle J N` is
continuous (`C^0`), `liftExpDomain g L` is open; when it is `C^m` (`m ≤ ∞`), `liftExp g L` is `C^m`
on `liftExpDomain g L`; when `V` is a `C^1` vector bundle and the lift is `C^1`, the differential
of `liftExp g L` at `zeroSection P V q` sends `(u, v)` (under `zeroSectionTangentEquiv`) to
`dg_q u + L q v`. When `g` is a topological embedding of a nonempty manifold `Q` and those
differentials along the zero section are invertible, `liftExp g L` restricts to a `C^m` partial
diffeomorphism near the zero section with target inside any prescribed open neighbourhood of
`range g`.

Specializing `g` to a smooth embedding `f : Q → N` and `L q` to `f.normalRepresentative q hn`
recovers the Riemannian normal exponential (`SmoothEmbedding.normalExp`), while composing
`i.normalRepresentative q hn` with a prescribed ambient tangent map
`A q : T_(i q) M →L[ℝ] T_(g q) N` yields the twisted normal exponential
(`SmoothEmbedding.twistedNormalExp`).

## Formal sources

Extracted from the Riemannian normal-exponential pipeline in
`TauCeti/Geometry/Manifold/TubularNeighborhood/Riemannian/Basic.lean`, `Regularity.lean`,
`Differential.lean`, and `Coordinates.lean`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set Function Topology TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.Bundle

section Defs

variable {F P G Q N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {V : Q → Type*} [∀ q, TopologicalSpace (V q)] [∀ q, AddCommMonoid (V q)] [∀ q, Module ℝ (V q)]

/-- The natural domain of the lifted Riemannian exponential: the total-space points `(q, v)` whose
tangent image `L q v` lies in the ambient Riemannian exponential domain `expDomain J N (g q)`. -/
def liftExpDomain (g : Q → N) (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) :
    Set (TotalSpace P V) :=
  {p | L p.proj p.2 ∈ Manifold.expDomain J N (g p.proj)}

/-- Membership in `liftExpDomain g L` means that `L p.proj p.2` lies in `expDomain J N (g p.proj)`.
-/
@[simp]
theorem mem_liftExpDomain (g : Q → N) (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q))
    (p : TotalSpace P V) :
    p ∈ liftExpDomain (P := P) g L ↔ L p.proj p.2 ∈ Manifold.expDomain J N (g p.proj) :=
  Iff.rfl

/-- Every point of the zero section lies in `liftExpDomain g L`. -/
theorem zeroSection_mem_liftExpDomain (g : Q → N)
    (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) (q : Q) :
    zeroSection P V q ∈ liftExpDomain (P := P) g L := by
  simp [mem_liftExpDomain, zeroSection]

/-- Every fibre slice of `liftExpDomain g L` is star-convex at zero. -/
theorem starConvex_liftExpDomain_fiber (g : Q → N)
    (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) (q : Q) :
    StarConvex ℝ 0 {v : V q | (⟨q, v⟩ : TotalSpace P V) ∈ liftExpDomain (P := P) g L} := by
  intro v hv a b _ha hb _hab
  simp only [mem_ofPred_eq, mem_liftExpDomain, smul_zero, zero_add, map_smul] at hv ⊢
  exact (Manifold.starConvex_expDomain (I := J) (M := N) (g q)).smul_mem hv hb (by linarith)

/-- The **lifted Riemannian exponential** along `g : Q → N` and `L : ∀ q, V q →L[ℝ] T_(g q) N`,
sending `(q, v)` to `exp^N_(g q) (L q v)`. Outside `liftExpDomain g L`, it takes the junk value
`g q` inherited from `Manifold.riemannianExp`. -/
def liftExp (g : Q → N) (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) (p : TotalSpace P V) : N :=
  Manifold.riemannianExp J N (g p.proj) (L p.proj p.2)

/-- Evaluating `liftExp g L` at `p` exponentiates `L p.proj p.2` at `g p.proj`. -/
theorem liftExp_apply (g : Q → N) (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q))
    (p : TotalSpace P V) :
    liftExp (P := P) g L p = Manifold.riemannianExp J N (g p.proj) (L p.proj p.2) :=
  (rfl)

/-- On the zero section, `liftExp g L` agrees with the base map `g`. -/
@[simp]
theorem liftExp_zeroSection [J.Boundaryless] [T2Space N] (g : Q → N)
    (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) (q : Q) :
    liftExp (P := P) g L (zeroSection P V q) = g q := by
  simp [liftExp_apply, zeroSection, Manifold.riemannianExp_zero]

/-- Outside `liftExpDomain g L`, `liftExp g L` takes the base value `g p.proj`. -/
@[simp]
theorem liftExp_of_notMem_liftExpDomain [J.Boundaryless] (g : Q → N)
    (L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)) {p : TotalSpace P V}
    (hp : p ∉ liftExpDomain (P := P) g L) :
    liftExp (P := P) g L p = g p.proj :=
  Manifold.riemannianExp_of_notMem_expDomain (mt (mem_liftExpDomain g L p).2 hp)

end Defs

section RegularityAndCoords

variable {E F P H G Q N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace Q] [ChartedSpace H Q]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [J.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {V : Q → Type*} [∀ q, AddCommMonoid (V q)] [∀ q, Module ℝ (V q)]
  [∀ q, TopologicalSpace (V q)] [TopologicalSpace (TotalSpace P V)]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace Q] [ChartedSpace H Q] in
/-- When the total-space lift `p ↦ (g p.proj, L p.proj p.2)` into `TangentBundle J N` is
continuous, `liftExpDomain g L` is open in `TotalSpace P V`. -/
theorem isOpen_liftExpDomain {g : Q → N} {L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)}
    (hL : Continuous fun p : TotalSpace P V ↦ (⟨g p.proj, L p.proj p.2⟩ : TangentBundle J N)) :
    IsOpen (liftExpDomain (P := P) g L) := by
  have : IsManifold J (0 + 1) N := by simpa using (inferInstance : IsManifold J 1 N)
  convert (Manifold.isOpen_setOfPred_mem_expDomain (I := J) (M := N)).preimage hL using 1
  ext p
  exact mem_liftExpDomain g L p

/-- When the total-space lift `p ↦ (g p.proj, L p.proj p.2)` into `TangentBundle J N` is `C^m`
(`m ≤ ∞`), `liftExp g L` is `C^m` on `liftExpDomain g L`. -/
theorem contMDiffOn_liftExp [FiberBundle P V] {m : ℕ∞ω} [ENat.LEInfty m]
    {g : Q → N} {L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)}
    (hL : ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, F)) m
      fun p : TotalSpace P V ↦ (⟨g p.proj, L p.proj p.2⟩ : TangentBundle J N)) :
    ContMDiffOn (I.prod 𝓘(ℝ, P)) J m (liftExp (P := P) g L) (liftExpDomain (P := P) g L) := by
  have hm' : m + 1 ≤ ∞ := by
    lift m to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
    exact_mod_cast le_top
  have : IsManifold J (m + 1) N := IsManifold.of_le hm'
  convert ((Manifold.contMDiffOn_riemannianExp_tangentBundle (I := J) (M := N)).of_le
    ENat.LEInfty.out).comp hL.contMDiffOn
    (fun p hp ↦ (mem_liftExpDomain g L p).mp hp) using 1
  funext p
  exact liftExp_apply g L p

/-- Under `zeroSectionTangentEquiv`, the differential of `liftExp g L` at `zeroSection P V q` sends
`(u, v)` to `dg_q u + L q v`. -/
theorem mfderiv_liftExp_zeroSection_apply
    [FiberBundle P V] [VectorBundle ℝ P V]
    {g : Q → N} {L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)}
    (hL : ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, F)) 1
      fun p : TotalSpace P V ↦ (⟨g p.proj, L p.proj p.2⟩ : TangentBundle J N))
    (q : Q) (u : TangentSpace I q) (v : V q) :
    mfderiv (I.prod 𝓘(ℝ, P)) J (liftExp (P := P) g L) (zeroSection P V q)
        ((zeroSectionTangentEquiv (I := I) q).symm (u, v)) =
      mfderiv I J g q u + L q v := by
  have : IsManifold J (1 + 1) N := .of_le (n := ∞) (by norm_cast)
  have he : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J (liftExp (P := P) g L) (zeroSection P V q) :=
    ((contMDiffOn_liftExp hL).contMDiffAt
      ((isOpen_liftExpDomain hL.continuous).mem_nhds
        (zeroSection_mem_liftExpDomain g L q))).mdifferentiableAt one_ne_zero
  rw [zeroSectionTangentEquiv_symm_eq, map_add]
  congr 1
  · have h := mfderiv_comp_apply q he (mdifferentiableAt_zeroSection ℝ V) u
    have hfun : liftExp (P := P) g L ∘ zeroSection P V = g := funext (liftExp_zeroSection g L)
    rw [hfun] at h
    exact h.symm
  · rw [zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → TotalSpace P V := fun t ↦ ⟨q, t • v⟩
    have hl : ContMDiff 𝓘(ℝ) (I.prod 𝓘(ℝ, P)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨q, v⟩ : TotalSpace P V)))
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) he
      (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    let w : TangentSpace J (g q) := L q v
    have hfun : liftExp (P := P) g L ∘ line =
        Manifold.riemannianExp J N (g q) ∘ (fun t : ℝ ↦ t • w) := by
      funext t
      simp only [Function.comp_apply, line, liftExp_apply, map_smul, w]
    rw [hfun] at h
    have hexp₀ := Manifold.hasMFDerivAt_riemannianExp_zero (I := J) (g q)
    have hvec : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace J (g q))
        (fun t : ℝ ↦ t • w) 0 (ContinuousLinearMap.toSpanSingleton ℝ w) :=
      (ContinuousLinearMap.toSpanSingleton ℝ w).hasMFDerivAt
    have hc := mfderiv_comp_apply_of_eq (0 : ℝ) hexp₀.mdifferentiableAt
      hvec.mdifferentiableAt (by simp) (1 : ℝ)
    have hc₁ := Manifold.mfderiv_riemannianExp_apply_zero (I := J) (g q)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace J (g q)) (fun t : ℝ ↦ t • w) (0 : ℝ) (1 : ℝ))
    have hc₂ : (mfderiv 𝓘(ℝ) 𝓘(ℝ, TangentSpace J (g q)) (fun t : ℝ ↦ t • w) (0 : ℝ) (1 : ℝ) :
        TangentSpace J (g q)) = ContinuousLinearMap.toSpanSingleton ℝ w (1 : ℝ) :=
      DFunLike.congr_fun hvec.mfderiv (1 : ℝ)
    have hone := ContinuousLinearMap.toSpanSingleton_apply_one (M₁ := TangentSpace J (g q)) ℝ w
    exact h.symm.trans (hc.trans (hc₁.trans (hc₂.trans hone)))

/-- When the total-space lift is `C^m` (`1 ≤ m ≤ ∞`) on a `C^m` vector bundle over a boundaryless
manifold `Q` and `mfderiv (liftExp g L)` is invertible at `zeroSection P V q`, `liftExp g L` is a
`C^m` local diffeomorphism at `zeroSection P V q`. -/
theorem isLocalDiffeomorphAt_liftExp_zeroSection [CompleteSpace E] [CompleteSpace P]
    [I.Boundaryless] {m : ℕ∞ω} [ENat.LEInfty m] [IsManifold I m Q]
    [FiberBundle P V] [VectorBundle ℝ P V] [ContMDiffVectorBundle m P V I]
    (hm1 : 1 ≤ m) {g : Q → N} {L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)}
    (hL : ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, F)) m
      fun p : TotalSpace P V ↦ (⟨g p.proj, L p.proj p.2⟩ : TangentBundle J N))
    {q : Q}
    (hinv : (mfderiv (I.prod 𝓘(ℝ, P)) J (liftExp (P := P) g L) (zeroSection P V q)).IsInvertible) :
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J m (liftExp (P := P) g L) (zeroSection P V q) := by
  have : IsManifold J m N := .of_le ENat.LEInfty.out
  obtain ⟨e, he⟩ := hinv
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_liftExp hL)
    (isOpen_liftExpDomain hL.continuous) (zeroSection_mem_liftExpDomain g L q)
    BoundarylessManifold.isInteriorPoint hm1 he

/-- When `g : Q → N` is a topological embedding of a nonempty finite-dimensional boundaryless
manifold `Q` into a second-countable Riemannian manifold `N` and `liftExp g L` is `C^m`
(`1 ≤ m ≤ ∞`) with invertible differential at every point of the zero section, `liftExp g L`
restricts to a single `C^m` partial diffeomorphism on an open neighbourhood of the zero section
with target inside any prescribed open neighbourhood `O` of `range g`. -/
theorem exists_partialDiffeomorph_liftExp_subset
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [I.Boundaryless]
    [SecondCountableTopology N] [Nonempty Q]
    {m : ℕ∞ω} [ENat.LEInfty m] [IsManifold I m Q]
    [FiberBundle P V] [VectorBundle ℝ P V] [ContMDiffVectorBundle m P V I]
    (hm1 : 1 ≤ m) {g : Q → N} (hg_emb : IsEmbedding g)
    {L : ∀ q : Q, V q →L[ℝ] TangentSpace J (g q)}
    (hL : ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, F)) m
      fun p : TotalSpace P V ↦ (⟨g p.proj, L p.proj p.2⟩ : TangentBundle J N))
    (hinv : ∀ q : Q,
      (mfderiv (I.prod 𝓘(ℝ, P)) J (liftExp (P := P) g L) (zeroSection P V q)).IsInvertible)
    {O : Set N} (hO : IsOpen O) (hgO : range g ⊆ O) :
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J (TotalSpace P V) N m,
      (∀ q, zeroSection P V q ∈ Φ.source) ∧
      Φ.source ⊆ liftExpDomain g L ∧ Φ.target ⊆ O ∧
      Φ.target = liftExp g L '' Φ.source ∧ ⇑Φ = liftExp g L := by
  have : T2Space Q := hg_emb.t2Space
  have : SecondCountableTopology Q := hg_emb.isInducing.secondCountableTopology
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : LocallyCompactSpace (ModelProd H P) := (I.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P V) := ChartedSpace.locallyCompactSpace (ModelProd H P) _
  have : MetrizableSpace N := Manifold.metrizableSpace J N
  have : MetrizableSpace (TotalSpace P V) := Manifold.metrizableSpace (I.prod 𝓘(ℝ, P)) _
  have : Nonempty (TotalSpace P V) := Nonempty.map (zeroSection P V) inferInstance
  let Ψ := liftExp (P := P) g L
  let U := {p | IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J m Ψ p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp ↦ hp.eventually
  let S := (U ∩ liftExpDomain (P := P) g L) ∩ Ψ ⁻¹' O
  have hS : IsOpen S :=
    ContinuousOn.isOpen_inter_preimage
      ((contMDiffOn_liftExp hL).continuousOn.mono inter_subset_right)
      (hU.inter (isOpen_liftExpDomain hL.continuous)) hO
  have hzero : range (zeroSection P V) ⊆ S := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨isLocalDiffeomorphAt_liftExp_zeroSection hm1 hL (hinv q),
      zeroSection_mem_liftExpDomain g L q⟩, by simpa [Ψ] using hgO (mem_range_self q)⟩
  have hlocal : IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, P)) J m Ψ S := fun p ↦ p.property.1.1
  have hcore : Ψ ∘ zeroSection P V = g := funext (liftExp_zeroSection g L)
  obtain ⟨Φ, hzeroΦ, hΦS, htarget, hΦ⟩ := hlocal.exists_partialDiffeomorph_near_section
    hS hzero (_root_.Bundle.Trivialization.continuous_zeroSection ℝ) (π P V)
    (FiberBundle.continuous_proj _ _) (fun _ ↦ rfl) (hcore ▸ hg_emb.isInducing)
  refine ⟨Φ, fun q ↦ hzeroΦ (mem_range_self q), fun p hp ↦ (hΦS hp).1.2, ?_, htarget, hΦ⟩
  rw [htarget]
  rintro _ ⟨p, hp, rfl⟩
  exact (hΦS hp).2

end RegularityAndCoords

end TauCeti.Bundle

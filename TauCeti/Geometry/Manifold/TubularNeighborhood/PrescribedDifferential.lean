/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Extending an embedding with a prescribed ambient differential

Let `i : Q → M` be a smooth embedding and `g : Q → N` a smooth map which induces the topology
of `Q`. Suppose that along `Q` we are given linear isomorphisms
`A q : T_{i q} M → T_{g q} N`, depending smoothly on `q` in tangent coordinates, which extend the
differential of `g` along `i`: `A q ∘ d i_q = d g_q`. Then there is a smooth partial
diffeomorphism `Ψ` from `M` to `N`, defined on an open neighbourhood of the image of `i`, with
`Ψ ∘ i = g` and with differential `A q` at every point `i q`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`). Its source and target can be
kept inside any prescribed open neighbourhoods of the two images. Neither compactness nor
closedness of the images is needed. Conversely, the restriction of any such `Ψ` to `i(Q)` and its
differentials there satisfy all these hypotheses, so they characterize the data realized by
partial diffeomorphisms (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq_iff`).

This is the differential-topology half of the neighbourhood theorem with prescribed ambient
derivative for symplectic germs: once `Ψ` realizes a symplectic bundle isomorphism `A` as its
differential, the pulled-back form agrees with the source form on the full ambient tangent
spaces along `Q`, and the relative Moser theorem corrects `Ψ` to a symplectomorphism with the
same differential. Data given over a diffeomorphism `f : Q → Q'` and an embedding `j : Q' → N`,
with `A q : T_{i q} M → T_{j (f q)} N`, is the case `g = j ∘ f`.

## Construction

Choose auxiliary Riemannian metrics on `M` and `N`. The normal exponential of `i` is a partial
diffeomorphism `Φ_M` from a neighbourhood of the zero section of the normal bundle `ν` of `i`
onto a neighbourhood of `i(Q)` (`SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`).
On `ν` consider

`Φ_N (q, n) = exp^N_{g q} (A q n)`,

where the normal class `n` is read as its orthogonal representative. Under the splitting of the
tangent space of `ν` along its zero section, the differentials at `(q, 0)` are
`d Φ_M (u, n) = d i_q u + n` and `d Φ_N (u, n) = d g_q u + A q n = A q (d i_q u + n)`, so
`d Φ_N = A q ∘ d Φ_M` there. Hence `Φ_N` is a local diffeomorphism along the zero section, and
since `Φ_N` restricted to the zero section is the embedding `g`, it is injective on a
neighbourhood of the zero section
(`TauCeti.exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt`). The composite
`Ψ = Φ_N ∘ Φ_M⁻¹` has the required properties.

## Main results

* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`: a partial diffeomorphism
  extending `g` along `i` with prescribed differential `A`, inside prescribed neighbourhoods.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq_iff`: the restriction and
  differentials of partial diffeomorphisms along `i` are exactly such data `(g, A)`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4 (the Lagrangian neighbourhood theorem, whose
  prescribed-derivative refinement this construction serves).
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3 (tubular neighbourhoods).
-/

public noncomputable section

open Bundle Manifold Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V F P H G H' Q M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} {K : ModelWithCorners ℝ F H'}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold K ∞ N]
  [K.Boundaryless] [T2Space N]

section Riemannian

variable [RiemannianBundle (fun y : M ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y)]
  [RiemannianBundle (fun y : N ↦ TangentSpace K y)]
  [IsContMDiffRiemannianBundle K ∞ F (fun y : N ↦ TangentSpace K y)]
  (i : SmoothEmbedding I J ∞ Q M) (hn : (∞ : ℕ∞ω) ≠ 0) {g : Q → N}
  (A : ∀ q, TangentSpace J (i q) →L[ℝ] TangentSpace K (g q))

/-- The exponential in `N` of the image under `A` of the orthogonal representative of a normal
vector of `i`. -/
private def transportedNormalExp (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) : N :=
  Manifold.riemannianExp K N (g p.proj) (A p.proj (i.normalRepresentative p.proj hn p.snd))

/-- The tangent vector of `N` whose exponential is `transportedNormalExp`. -/
private def transportedNormalVector (p : TotalSpace P (fun q ↦ i.NormalSpace q hn)) :
    TangentBundle K N :=
  ⟨g p.proj, A p.proj (i.normalRepresentative p.proj hn p.snd)⟩

omit [FiniteDimensional ℝ F] [K.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace K y)]
  [IsContMDiffRiemannianBundle K ∞ F (fun y : N ↦ TangentSpace K y)] in
/-- The transported normal vector depends smoothly on the normal vector. -/
private theorem contMDiff_transportedNormalVector
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q) :
    letI := i.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) K.tangent ∞ (transportedNormalVector (P := P) i hn A) := by
  let := i.normalSpaceFiberBundle hn hdim
  have hproj : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞
      (fun p : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦ p.proj) :=
    contMDiff_proj _
  intro p
  -- `clm_apply_of_inCoordinates` takes `A` in the `ContinuousLinearMap.inCoordinates` form, so `hϕ`
  -- is stated that way; `inTangentCoordinates` in `hA` is by definition this `inCoordinates`.
  have hϕ : ContMDiffAt (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, V →L[ℝ] F) ∞
      (fun p' : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦
        ContinuousLinearMap.inCoordinates V (TangentSpace J (M := M)) F
          (TangentSpace K (M := N)) (i p.proj) (i p'.proj) (g p.proj) (g p'.proj)
          (A p'.proj)) p :=
    (hA p.proj).comp p (hproj p)
  have hv : ContMDiffAt (I.prod 𝓘(ℝ, P)) J.tangent ∞
      (fun p' : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦
        (⟨i p'.proj, i.normalRepresentative p'.proj hn p'.snd⟩ : TangentBundle J M)) p :=
    i.contMDiff_normalRepresentative (m := ∞) hn (by simp) hdim p
  exact ContMDiffAt.clm_apply_of_inCoordinates (F₁ := V) (E₁ := TangentSpace J (M := M))
    (F₂ := F) (E₂ := TangentSpace K (M := N)) (b₁ := fun p ↦ i p.proj)
    (b₂ := fun p ↦ g p.proj) (ϕ := fun p ↦ A p.proj) (m₀ := p)
    (v := fun p ↦ i.normalRepresentative p.proj hn p.snd) hϕ hv ((hg.comp hproj) p)

/-- The natural domain of `transportedNormalExp`. -/
private def transportedNormalExpDomain : Set (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
  transportedNormalVector i hn A ⁻¹' {z | z.snd ∈ Manifold.expDomain K N z.proj}

/-- The natural domain of the transported normal exponential is open. -/
private theorem isOpen_transportedNormalExpDomain
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q) :
    letI := i.normalSpaceFiberBundle hn hdim
    IsOpen (transportedNormalExpDomain (P := P) i hn A) := by
  let := i.normalSpaceFiberBundle hn hdim
  exact Manifold.isOpen_setOfPred_mem_expDomain.preimage
    (contMDiff_transportedNormalVector i hn A hdim hg hA).continuous

omit [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [IsManifold I ∞ Q] [IsManifold J ∞ M] [K.Boundaryless] [T2Space N]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y)] in
/-- The zero section lies in the natural domain of the transported normal exponential. -/
private theorem zeroSection_mem_transportedNormalExpDomain (q : Q) :
    zeroSection P (fun q ↦ i.NormalSpace q hn) q ∈ transportedNormalExpDomain i hn A := by
  -- The fibre value of the zero section is the zero of the fibre over its projection, which is
  -- only definitionally the fibre over `q`; restate it over `q` so that `map_zero` applies.
  change A q (i.normalRepresentative q hn 0) ∈ Manifold.expDomain K N (g q)
  rw [map_zero, map_zero]
  exact Manifold.zero_mem_expDomain (I := K) (M := N) (g q)

/-- The transported normal exponential is smooth on its natural domain. -/
private theorem contMDiffOn_transportedNormalExp
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q) :
    letI := i.normalSpaceFiberBundle hn hdim
    ContMDiffOn (I.prod 𝓘(ℝ, P)) K ∞ (transportedNormalExp (P := P) i hn A)
      (transportedNormalExpDomain i hn A) := by
  let := i.normalSpaceFiberBundle hn hdim
  exact Manifold.contMDiffOn_riemannianExp_tangentBundle.comp
    (contMDiff_transportedNormalVector i hn A hdim hg hA).contMDiffOn fun _ hp ↦ hp

omit [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [IsManifold I ∞ Q] [IsManifold J ∞ M]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y)] [K.Boundaryless]
  [T2Space N] in
/-- The transported normal exponential is the fibrewise exponential of `A` composed with the
orthogonal representative of a normal vector. -/
private theorem transportedNormalExp_eq :
    transportedNormalExp i hn A = fun p : TotalSpace P (fun q ↦ i.NormalSpace q hn) ↦
      Manifold.riemannianExp K N (g p.proj)
        ((A p.proj).comp (i.normalRepresentative p.proj hn) p.snd) := by
  funext p
  rw [ContinuousLinearMap.comp_apply, transportedNormalExp]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [IsManifold I ∞ Q] [IsManifold J ∞ M]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y)] in
/-- The transported normal exponential sends the zero section to `g`. -/
private theorem transportedNormalExp_zeroSection (q : Q) :
    transportedNormalExp i hn A (zeroSection P (fun q ↦ i.NormalSpace q hn) q) = g q := by
  rw [transportedNormalExp_eq]
  exact Bundle.riemannianExp_fiberwise_zeroSection
    (fun q ↦ (A q).comp (i.normalRepresentative q hn)) q

/-- Under the splitting of the tangent space along the zero section, the differential of the
transported normal exponential sends `(u, n)` to `d g u + A n`, the normal class `n` being read
as its orthogonal representative. -/
private theorem mfderiv_transportedNormalExp_zeroSection_apply
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (q : Q) (u : TangentSpace I q) (v : i.NormalSpace q hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    mfderiv (I.prod 𝓘(ℝ, P)) K (transportedNormalExp i hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q)
        ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (u, v)) =
      mfderiv I K g q u + A q (i.normalRepresentative q hn v) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have he : MDifferentiableAt (I.prod 𝓘(ℝ, P)) K (transportedNormalExp i hn A)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q) :=
    ((contMDiffOn_transportedNormalExp i hn A hdim hg hA).contMDiffAt
      ((isOpen_transportedNormalExpDomain i hn A hdim hg hA).mem_nhds
        (zeroSection_mem_transportedNormalExpDomain i hn A q))).mdifferentiableAt (by simp)
  rw [transportedNormalExp_eq] at he ⊢
  exact Bundle.mfderiv_riemannianExp_fiberwise_zeroSection_apply
    (fun q ↦ (A q).comp (i.normalRepresentative q hn)) q he u v

/-- Along the zero section, the differential of the transported normal exponential is `A`
composed with the differential of the normal exponential of `i`. -/
private theorem mfderiv_transportedNormalExp_zeroSection [J.Boundaryless] [T2Space M]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q) (q : Q) :
    letI := i.normalSpaceFiberBundle hn hdim
    mfderiv (I.prod 𝓘(ℝ, P)) K (transportedNormalExp i hn A)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q) =
      (A q).comp (mfderiv (I.prod 𝓘(ℝ, P)) J (i.normalExp (P := P) hn)
        (zeroSection P (fun q ↦ i.NormalSpace q hn) q)) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  ext w
  obtain ⟨⟨u, v⟩, rfl⟩ := (Bundle.zeroSectionTangentEquiv (I := I) q).symm.surjective w
  rw [mfderiv_transportedNormalExp_zeroSection_apply i hn A hdim hg hA, ← hAi q,
    ContinuousLinearMap.comp_apply, ← map_add]
  -- The composite on the right is typed over the tangent space of `M` at `normalExp (Z q)`, which
  -- is only definitionally the tangent space at `i q` on which `A q` acts; `erw` sees through.
  erw [ContinuousLinearMap.comp_apply]
  exact congrArg (A q) (i.mfderiv_normalExp_zeroSection_apply hn (by simp) hdim q u v).symm

/-- The transported normal exponential is a local diffeomorphism at every zero normal vector. -/
private theorem isLocalDiffeomorphAt_transportedNormalExp_zeroSection [I.Boundaryless]
    [J.Boundaryless] [T2Space M]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q) (q : Q) :
    letI := i.normalSpaceFiberBundle hn hdim
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) K ∞ (transportedNormalExp i hn A)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  obtain ⟨e, he⟩ : (mfderiv (I.prod 𝓘(ℝ, P)) K (transportedNormalExp i hn A)
      (zeroSection P (fun q ↦ i.NormalSpace q hn) q)).IsInvertible := by
    rw [mfderiv_transportedNormalExp_zeroSection i hn A hdim hg hA hAi q]
    exact (hAinv q).comp (i.isInvertible_mfderiv_normalExp_zeroSection hn (by simp) hdim q)
  exact isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_transportedNormalExp i hn A hdim hg hA)
    (isOpen_transportedNormalExpDomain i hn A hdim hg hA)
    (zeroSection_mem_transportedNormalExpDomain i hn A q) BoundarylessManifold.isInteriorPoint
    (by simp) he

/-- The transported normal exponential is a partial diffeomorphism on a neighbourhood of the zero
section, with image inside a prescribed open neighbourhood of the image of `g`. -/
private theorem exists_partialDiffeomorph_transportedNormalExp [I.Boundaryless] [Nonempty Q]
    [SecondCountableTopology M] [SecondCountableTopology N] [J.Boundaryless] [T2Space M]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (hg : ContMDiff I K ∞ g) (hgi : IsInducing g)
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q)
    {O' : Set N} (hO' : IsOpen O') (hgO' : range g ⊆ O') :
    letI := i.normalSpaceFiberBundle hn hdim
    ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) K (TotalSpace P (fun q ↦ i.NormalSpace q hn)) N ∞,
      (∀ q, zeroSection P (fun q ↦ i.NormalSpace q hn) q ∈ Φ.source) ∧ Φ.target ⊆ O' ∧
        ⇑Φ = transportedNormalExp i hn A := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : T2Space Q := i.isEmbedding.t2Space
  have : SecondCountableTopology Q := i.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace H' := K.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  have : MetrizableSpace N := Manifold.metrizableSpace K N
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace H Q
  have : MetrizableSpace (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
    Manifold.metrizableSpace (I.prod 𝓘(ℝ, P)) _
  have : Nonempty (TotalSpace P (fun q ↦ i.NormalSpace q hn)) :=
    Nonempty.map (zeroSection P (fun q ↦ i.NormalSpace q hn)) inferInstance
  have hTZ : transportedNormalExp i hn A ∘ zeroSection P (fun q ↦ i.NormalSpace q hn) = g :=
    funext (transportedNormalExp_zeroSection i hn A)
  obtain ⟨Φ, hΦZ, -, hΦO', -, hΦ⟩ := exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt
    (isLocalDiffeomorphAt_transportedNormalExp_zeroSection i hn A hdim hg hA hAinv hAi)
    (isOpen_transportedNormalExpDomain i hn A hdim hg hA)
    (range_subset_iff.2 (zeroSection_mem_transportedNormalExpDomain i hn A)) hO'
    (by rw [hTZ]; exact hgO') (_root_.Bundle.Trivialization.continuous_zeroSection ℝ)
    (π P (fun q ↦ i.NormalSpace q hn))
    (FiberBundle.continuous_proj _ _) (fun _ ↦ rfl) (by rw [hTZ]; exact hgi)
  exact ⟨Φ, fun q ↦ hΦZ (mem_range_self q), hΦO', hΦ⟩

end Riemannian

variable [RiemannianBundle (fun y : M ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y)]
  [RiemannianBundle (fun y : N ↦ TangentSpace K y)]
  [IsContMDiffRiemannianBundle K ∞ F (fun y : N ↦ TangentSpace K y)] in
/-- `exists_partialDiffeomorph_mfderiv_eq` for given Riemannian metrics on `M` and `N`. -/
private theorem exists_partialDiffeomorph_mfderiv_eq_of_riemannian [I.Boundaryless]
    [J.Boundaryless] [T2Space M]
    [Nonempty Q] [SecondCountableTopology M] [SecondCountableTopology N]
    (i : SmoothEmbedding I J ∞ Q M) {g : Q → N}
    (hg : ContMDiff I K ∞ g) (hgi : IsInducing g)
    {A : ∀ q, TangentSpace J (i q) →L[ℝ] TangentSpace K (g q)}
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q)
    {O : Set M} (hO : IsOpen O) (hiO : range i ⊆ O)
    {O' : Set N} (hO' : IsOpen O') (hgO' : range g ⊆ O') :
    ∃ Ψ : PartialDiffeomorph J K M N ∞, range i ⊆ Ψ.source ∧ Ψ.source ⊆ O ∧
      Ψ.target ⊆ O' ∧ (∀ q, Ψ (i q) = g q) ∧ ∀ q, mfderiv J K Ψ (i q) = A q := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The normal bundle of `i`, with a model fibre of the right dimension.
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E :=
    finrank_euclideanSpace_fin
  let := i.normalSpaceFiberBundle hn hdim
  let Z := zeroSection P (fun q ↦ i.NormalSpace q hn)
  -- `Φ_M`: normal-exponential coordinates around the image of `i`, inside `O`.
  obtain ⟨ΦM, hΦMZ, -, hΦMO, -, hΦM⟩ :=
    i.exists_partialDiffeomorph_normalExp_subset (P := P) (m := ∞) hn (by simp) (by simp) hdim
      hO hiO
  have hΦMz (q : Q) : ΦM (Z q) = i q := by rw [hΦM]; exact i.normalExp_zeroSection hn q
  -- `Φ_N`: the transported normal exponential, with image inside `O'`.
  obtain ⟨ΦN, hΦNZ, hΦNO', hΦN⟩ := exists_partialDiffeomorph_transportedNormalExp i hn A hdim hg
    hgi hA hAinv hAi hO' hgO'
  -- `Ψ = Φ_N ∘ Φ_M⁻¹`.
  have hΦMs (q : Q) : ΦM.symm (i q) = Z q := by rw [← hΦMz q]; exact ΦM.left_inv (hΦMZ q)
  refine ⟨ΦM.symm.trans ΦN, range_subset_iff.2 fun q ↦ ?_, ?_, ?_, fun q ↦ ?_, fun q ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    refine ⟨hΦMz q ▸ ΦM.map_source (hΦMZ q), ?_⟩
    rw [mem_preimage, hΦMs q]
    exact hΦNZ q
  · exact inter_subset_left.trans hΦMO
  · exact inter_subset_left.trans hΦNO'
  · rw [PartialDiffeomorph.coe_trans, comp_apply, hΦMs q, hΦN]
    exact transportedNormalExp_zeroSection i hn A q
  -- Along the zero section `d Φ_N = A ∘ d Φ_M`, and `d Φ_M` is onto. Both sides are ascribed to
  -- the model spaces `V →L[ℝ] F`: the tangent spaces at `ΦM (Z q)` and at `i q` are both
  -- definitionally `V`, so `key` can be stated before the base point `ΦM (Z q)` is rewritten to
  -- `i q`, which the dependent type of `A q` would otherwise block.
  have key : (mfderiv J K (ΦM.symm.trans ΦN) (ΦM (Z q)) : V →L[ℝ] F) = (A q : V →L[ℝ] F) := by
    ext w
    obtain ⟨x, rfl⟩ := (ΦM.isInvertible_mfderiv (by simp) (hΦMZ q)).surjective w
    rw [ΦM.mfderiv_symm_trans_apply_mfderiv_apply ΦN (by simp) (hΦMZ q) (hΦNZ q), hΦN,
      mfderiv_transportedNormalExp_zeroSection i hn A hdim hg hA hAi q, ← hΦM]
    -- Applying a composite of continuous linear maps is applying the two maps in turn; the
    -- composite is typed over the tangent spaces, which are only definitionally the model spaces
    -- of `key`, so `erw` sees through this.
    erw [ContinuousLinearMap.comp_apply]
  rw [hΦMz q] at key
  exact key

/-- **Extension with a prescribed ambient differential.** Let `i : Q → M` be a smooth embedding
and `g : Q → N` a smooth map inducing the topology of `Q`, between finite-dimensional
boundaryless real manifolds with `Q` nonempty and `M` and `N` Hausdorff and second countable. Let
`A q : T_{i q} M → T_{g q} N` be linear isomorphisms which are smooth in tangent coordinates and
satisfy `A q ∘ d i_q = d g_q`. Then there is a smooth partial diffeomorphism `Ψ` from `M` to `N`
whose source contains the image of `i` and lies in a prescribed open neighbourhood `O` of it,
whose target lies in a prescribed open neighbourhood `O'` of the image of `g`, with
`Ψ (i q) = g q` and `d Ψ_{i q} = A q` for every `q`. No compactness is required. -/
theorem exists_partialDiffeomorph_mfderiv_eq [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [Nonempty Q] [SecondCountableTopology M] [SecondCountableTopology N]
    (i : SmoothEmbedding I J ∞ Q M) {g : Q → N}
    (hg : ContMDiff I K ∞ g) (hgi : IsInducing g)
    {A : ∀ q, TangentSpace J (i q) →L[ℝ] TangentSpace K (g q)}
    (hA : ∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q)
    {O : Set M} (hO : IsOpen O) (hiO : range i ⊆ O)
    {O' : Set N} (hO' : IsOpen O') (hgO' : range g ⊆ O') :
    ∃ Ψ : PartialDiffeomorph J K M N ∞, range i ⊆ Ψ.source ∧ Ψ.source ⊆ O ∧
      Ψ.target ⊆ O' ∧ (∀ q, Ψ (i q) = g q) ∧ ∀ q, mfderiv J K Ψ (i q) = A q := by
  -- Auxiliary smooth Riemannian metrics on `M` and `N`.
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace H' := K.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace G M
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨gM⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := V)
    (E := fun y : M ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : M ↦ TangentSpace J y) := ⟨gM.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ V (fun y : M ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle gM
  obtain ⟨gN⟩ := nonempty_contMDiffRiemannianMetric (IB := K) (n := ⊤) (F := F)
    (E := fun y : N ↦ TangentSpace K y)
  let : RiemannianBundle (fun y : N ↦ TangentSpace K y) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle K ∞ F (fun y : N ↦ TangentSpace K y) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  exact exists_partialDiffeomorph_mfderiv_eq_of_riemannian i hg hgi hA hAinv hAi hO hiO
    hO' hgO'

/-- **Germs with a prescribed ambient differential.** Along a smooth embedding `i : Q → M` of a
nonempty manifold, a map
`g : Q → N` and linear maps `A q : T_{i q} M → T_{g q} N` are the restriction and the differentials
along `i(Q)` of a smooth partial diffeomorphism `Ψ` from `M` to `N` defined near `i(Q)` exactly
when `g` is smooth and induces the topology of `Q`, each `A q` is invertible, `A` is smooth in
tangent coordinates, and `A q ∘ d i_q = d g_q`. -/
theorem exists_partialDiffeomorph_mfderiv_eq_iff [I.Boundaryless] [J.Boundaryless] [T2Space M]
    [Nonempty Q] [SecondCountableTopology M] [SecondCountableTopology N]
    (i : SmoothEmbedding I J ∞ Q M) {g : Q → N}
    {A : ∀ q, TangentSpace J (i q) →L[ℝ] TangentSpace K (g q)} :
    (∃ Ψ : PartialDiffeomorph J K M N ∞, range i ⊆ Ψ.source ∧ (∀ q, Ψ (i q) = g q) ∧
        ∀ q, mfderiv J K Ψ (i q) = A q) ↔
      ContMDiff I K ∞ g ∧ IsInducing g ∧
        (∀ q, ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i g A q) q) ∧
        (∀ q, (A q).IsInvertible) ∧ ∀ q, (A q).comp (mfderiv I J i q) = mfderiv I K g q := by
  refine ⟨fun ⟨Ψ, hsrc, hval, hd⟩ ↦ ?_, fun ⟨hg, hgi, hA, hAinv, hAi⟩ ↦ ?_⟩
  · obtain rfl : g = Ψ ∘ i := funext fun q ↦ (hval q).symm
    obtain rfl : A = fun q ↦ mfderiv J K Ψ (i q) := funext fun q ↦ (hd q).symm
    have hiS (q : Q) : i q ∈ Ψ.source := hsrc (mem_range_self q)
    have hΨ (q : Q) : ContMDiffAt J K ∞ Ψ (i q) :=
      Ψ.contMDiffOn.contMDiffAt (Ψ.open_source.mem_nhds (hiS q))
    refine ⟨fun q ↦ (hΨ q).comp q (i.contMDiff q), ?_, fun q ↦ ?_, fun q ↦ ?_, fun q ↦ ?_⟩
    · -- `Ψ` is a homeomorphism of its source onto its target, and `i` lands in the source.
      exact Ψ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isInducing.comp
        (i.isEmbedding.isInducing.codRestrict hiS)
    · exact ContMDiffAt.mfderiv (fun _ ↦ Ψ) i ((hΨ q).comp (q, i q) contMDiffAt_snd)
        (i.contMDiff q) (by simp)
    · exact (PartialDiffeomorph.isLocalDiffeomorphAt J K ∞ Ψ (hiS q)).isInvertible_mfderiv
        (by simp)
    · exact (mfderiv_comp q ((hΨ q).mdifferentiableAt (by simp))
        ((i.contMDiff q).mdifferentiableAt (by simp))).symm
  · obtain ⟨Ψ, hsrc, -, -, hval, hd⟩ := i.exists_partialDiffeomorph_mfderiv_eq hg hgi hA hAinv
      hAi isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
    exact ⟨Ψ, hsrc, hval, hd⟩

end TauCeti.SmoothEmbedding

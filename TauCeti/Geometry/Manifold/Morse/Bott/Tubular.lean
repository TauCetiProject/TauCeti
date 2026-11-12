/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.NormalExp
public import TauCeti.Geometry.Manifold.Morse.Bott.VectorBundle
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The Morse–Bott lemma on the normal bundle

Let `i : S → M` be a smooth embedding into a boundaryless finite-dimensional manifold which is a
nondegenerate critical submanifold of `f : M → ℝ`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`), and let `ν` be its intrinsic
normal bundle, with fibres `TₛM ⧸ TₛS` (`TauCeti.SmoothEmbedding.NormalSpace`). On each fibre the
normal Hessian `Hessₛ` (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`) is a
nondegenerate symmetric bilinear form. This file proves the **Morse–Bott lemma on the normal
bundle**: there is a partial diffeomorphism `Θ` from the total space of `ν` to `M`, whose source
contains the whole zero section, which sends the zero section to `i` and puts `f` in fibrewise
quadratic form,

`f (Θ x) = f (i s) + ½ Hessₛ (x, x)` for `x` in the fibre over `s`.

Its image can be chosen inside any open neighbourhood of the image of `i`, and neither `S` nor
its image needs to be compact or closed. So near a Morse–Bott critical submanifold, `f` is its
critical value plus the normal Hessian on the fibres of a tubular neighbourhood. This is the local
model in which the negative disc bundle of the submanifold is attached when its critical level is
crossed.

The map `Θ` is the normal exponential of an auxiliary Riemannian metric
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`) composed with the inverse
of the fibre-preserving coordinate change given by the parametric Morse lemma on a vector bundle
(`TauCeti.exists_parametric_morse_partialDiffeomorph`). Its hypotheses hold because the restriction
of `f ∘ exp` to a fibre has a critical point at `0` whose Hessian is the normal Hessian
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_fiber_zero_apply`).
Fibrewise derivatives are taken for the quotient norm of the normal spaces, whose topology is
their quotient topology; neither this norm nor the metric appears in the statement.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`: the
  Morse–Bott lemma on the normal bundle.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, Theorem 15.1,
  p. 143.
-/

public noncomputable section

open Bundle Manifold Set Function Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}

section QuotientNorm

variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)] (i) (hn : (∞ : ℕ∞ω) ≠ 0) (s : S)

/-- The quotient norm on the normal space at `s`. Its topology is by definition the quotient
topology of the normal space, and its group structure that of the normal space. -/
private abbrev normalSpaceNormedAddCommGroup : NormedAddCommGroup (i.NormalSpace s hn) :=
  haveI : IsClosed (i.tangentRange s hn : Set (TangentSpace I (i s))) :=
    i.isClosed_tangentRange s hn
  let N := Submodule.Quotient.normedAddCommGroup (i.tangentRange s hn)
  -- Restate the group and the uniform structure with the quotient group and the quotient topology
  -- of the normal space as literal fields, so that instances built on them are found for the
  -- normed structure.
  { N with
    toAddCommGroup := inferInstance
    toUniformSpace := { N.toUniformSpace with toTopologicalSpace := inferInstance } }

/-- The normed space structure of the quotient norm on the normal space at `s`. -/
private abbrev normalSpaceNormedSpace :
    letI := normalSpaceNormedAddCommGroup i hn s
    NormedSpace ℝ (i.NormalSpace s hn) :=
  letI := normalSpaceNormedAddCommGroup i hn s
  { Submodule.Quotient.normedSpace (i.tangentRange s hn) ℝ with toModule := inferInstance }

end QuotientNorm

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y)] (hn : (∞ : ℕ∞ω) ≠ 0) (s : S)

namespace IsCriticalSubmanifold

omit [I.Boundaryless] [T2Space M] in
/-- The normal slice through the normal exponential, read on the intrinsic normal space, is the
normal slice on the orthogonal normal space precomposed with the orthogonal-representative
equivalence. -/
private theorem comp_normalExp_mk_eq_comp :
    (fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) =
      (fun w : (i.tangentRange s hn)ᗮ ↦
        f (i.normalExp (P := P) hn ⟨s, i.normalClass s hn w⟩)) ∘
        i.normalSpaceOrthogonalComplementEquiv s hn := by
  ext v
  rw [comp_apply, ← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

variable (h : i.IsCriticalSubmanifold f)
include h

/-- The restriction of `f ∘ exp` to the normal fibre over `s` is critical at `0`. -/
private theorem fderiv_comp_normalExp_mk_zero :
    letI := normalSpaceNormedAddCommGroup i hn s
    letI := normalSpaceNormedSpace i hn s
    fderiv ℝ (fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) 0 = 0 := by
  let := normalSpaceNormedAddCommGroup i hn s
  let := normalSpaceNormedSpace i hn s
  rw [comp_normalExp_mk_eq_comp, ContinuousLinearEquiv.comp_right_fderiv, map_zero,
    h.fderiv_comp_normalExp_fiber_zero hn s, ContinuousLinearMap.zero_comp]

/-- The Hessian at `0` of the restriction of `f ∘ exp` to the normal fibre over `s` is the normal
Hessian. -/
private theorem fderiv_fderiv_comp_normalExp_mk_zero_apply (u w : i.NormalSpace s hn) :
    letI := normalSpaceNormedAddCommGroup i hn s
    letI := normalSpaceNormedSpace i hn s
    fderiv ℝ (fderiv ℝ fun v : i.NormalSpace s hn ↦ f (i.normalExp (P := P) hn ⟨s, v⟩)) 0 u w =
      h.normalHessian hn s u w := by
  let := normalSpaceNormedAddCommGroup i hn s
  let := normalSpaceNormedSpace i hn s
  rw [comp_normalExp_mk_eq_comp, ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply,
    map_zero, h.fderiv_fderiv_comp_normalExp_fiber_zero_apply hn s,
    ← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ← normalSpaceOrthogonalComplementEquiv_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- For a Morse–Bott submanifold, the Hessian at `0` of the restriction of `f ∘ exp` to a normal
fibre is invertible. -/
private theorem isInvertible_fderiv_fderiv_comp_normalExp_mk_zero :
    letI := normalSpaceNormedAddCommGroup i hn s
    letI := normalSpaceNormedSpace i hn s
    (fderiv ℝ (fderiv ℝ fun v : i.NormalSpace s hn ↦
      f (i.normalExp (P := P) hn ⟨s, v⟩)) 0).IsInvertible := by
  let := normalSpaceNormedAddCommGroup i hn s
  let := normalSpaceNormedSpace i hn s
  refine ContinuousLinearMap.isInvertible_of_injective (𝕜 := ℝ) (E := i.NormalSpace s hn) ?_
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  -- A vector killed by the Hessian lies in the kernel of the normal Hessian, which is trivial.
  have hu' : h.normalHessian hn s u = 0 := LinearMap.ext fun w ↦ by
    rw [← h.toIsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_mk_zero_apply (P := P) hn s u w,
      hu]
    rfl
  simpa [h.ker_normalHessian hn s] using (LinearMap.mem_ker.2 hu' : u ∈ LinearMap.ker _)

omit [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y)] in
/-- **The Morse–Bott lemma on the normal bundle.** Let `i : S → M` be a nondegenerate critical
submanifold of `f`, for a smooth embedding of a nonempty manifold into a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, and let `f` be `C^{k+2}`,
`1 ≤ k ≤ ∞`, on an open neighbourhood `O` of the image of `i`. Then there is a `C^k` partial
diffeomorphism `Θ` from the total space of the intrinsic normal bundle of `i` to `M`, whose source
contains the whole zero section, which sends the zero section to `i` and has image in `O`, such
that `f (Θ x) = f (i s) + ½ Hessₛ (x, x)` for every `x` in its source over `s`, where `Hessₛ` is
the normal Hessian. -/
theorem exists_morseBott_partialDiffeomorph_normalBundle [SecondCountableTopology M] [Nonempty S]
    [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J ∞ S]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {k : ℕ∞} (hk : k ≠ 0) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    {O : Set M} (hO : IsOpen O) (hiO : range i ⊆ O) (hf : ContMDiffOn I 𝓘(ℝ) (k + 2) f O) :
    letI := i.normalSpaceFiberBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P (fun s ↦ i.NormalSpace s hn)) M k,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧ Θ.target ⊆ O ∧
      ∀ x ∈ Θ.source, f (Θ x) = f (i x.proj) + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2 := by
  let := i.normalSpaceFiberBundle hn hdim
  have hk2 : (k : ℕ∞ω) + 2 ≤ ∞ := by
    rw [← WithTop.coe_ofNat, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 le_top
  -- An auxiliary smooth Riemannian metric on `M`, for the normal exponential.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun y : M ↦ TangentSpace I y)
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : T2Space S := i.isEmbedding.t2Space
  have : SecondCountableTopology S := i.isEmbedding.isInducing.secondCountableTopology
  have : IsManifold J (k + 2) S := .of_le hk2
  let := i.normalSpaceVectorBundle hn hdim
  have := i.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  have : ContMDiffVectorBundle (k + 2) P (fun s ↦ i.NormalSpace s hn) J := .of_le hk2
  -- Step 1: the normal exponential `Φ₀` is a partial diffeomorphism near the zero section, and
  -- `f ∘ Φ₀` is `C^{k+2}` on its source.
  obtain ⟨Φ₀, hΦ₀zero, -, hΦ₀O, -, hΦ₀⟩ := i.exists_partialDiffeomorph_normalExp_subset (P := P)
    (m := ∞) hn (by simp) (by simp) hdim hO hiO
  have hg : ContMDiffOn (J.prod 𝓘(ℝ, P)) 𝓘(ℝ) (k + 2) (fun x ↦ f (i.normalExp (P := P) hn x))
      Φ₀.source := by
    rw [← hΦ₀]
    exact hf.comp (Φ₀.contMDiffOn.of_le hk2) fun x hx ↦ hΦ₀O (Φ₀.map_source hx)
  -- Step 2: the parametric Morse lemma puts `f ∘ Φ₀` in fibrewise normal form through a
  -- fibre-preserving `Φ x = ⟨x.proj, ψ x⟩` which fixes the zero section.
  let := fun s ↦ normalSpaceNormedAddCommGroup i hn s
  let := fun s ↦ normalSpaceNormedSpace i hn s
  obtain ⟨ψ, Φ, hΦzero, -, hΦ, -, hψ, hnf⟩ := exists_parametric_morse_partialDiffeomorph
    (IB := J) (F := P) (E := fun s ↦ i.NormalSpace s hn) (n := k) Φ₀.open_source hΦ₀zero hg
    (fun s ↦ h.toIsCriticalSubmanifold.fderiv_comp_normalExp_mk_zero (P := P) hn s)
    (fun s ↦ h.isInvertible_fderiv_fderiv_comp_normalExp_mk_zero (P := P) hn s) hk
  have hΦz (s : S) : Φ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) =
      zeroSection P (fun s ↦ i.NormalSpace s hn) s := by
    rw [hΦ, hψ]
    rfl
  have hΦsz (s : S) : Φ.symm (zeroSection P (fun s ↦ i.NormalSpace s hn) s) =
      zeroSection P (fun s ↦ i.NormalSpace s hn) s := by
    conv_lhs => rw [← hΦz s]
    exact Φ.left_inv (hΦzero s)
  -- Step 3: `Θ = Φ₀ ∘ Φ⁻¹`.
  refine ⟨Φ.symm.trans (Φ₀.ofLE (WithTop.coe_le_coe.2 le_top)), fun s ↦ ?_, fun s ↦ ?_, ?_,
    fun x hx ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    refine ⟨hΦz s ▸ Φ.map_source (hΦzero s), ?_⟩
    rw [mem_preimage, hΦsz s]
    simpa using hΦ₀zero s
  · rw [PartialDiffeomorph.coe_trans, comp_apply, hΦsz s]
    simp [hΦ₀]
  · rw [PartialDiffeomorph.trans_target]
    simpa using inter_subset_left.trans hΦ₀O
  · rw [PartialDiffeomorph.trans_source] at hx
    -- Write `x = Φ y = ⟨y.proj, ψ y⟩` and apply the normal form of `f ∘ Φ₀` at `y`.
    have hx' : x = ⟨(Φ.symm x).proj, ψ (Φ.symm x)⟩ := (Φ.right_inv hx.1).symm.trans (hΦ _)
    have hy : Φ.symm x ∈ Φ.source := Φ.map_target hx.1
    have key := hnf _ hy
    rw [PartialDiffeomorph.coe_trans, comp_apply]
    generalize Φ.symm x = y at hy hx' key ⊢
    subst hx'
    rw [h.toIsCriticalSubmanifold.fderiv_fderiv_comp_normalExp_mk_zero_apply (P := P),
      normalExp_zeroSection] at key
    simpa [hΦ₀] using key

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding

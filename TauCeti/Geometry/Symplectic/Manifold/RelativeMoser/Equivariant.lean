/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
public import TauCeti.Geometry.Manifold.DifferentialForm.Average
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.GroupAction.InvariantCutoff
import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
import TauCeti.Geometry.Manifold.GroupAction.Restrict
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The equivariant relative Moser theorem

Let a compact group `G`, itself a smooth manifold, act smoothly on a boundaryless Hausdorff manifold
`M`, modelled on a finite-dimensional space, preserving two closed two-forms `σ₀` and `σ₁`. Let `K`
be an invariant compact set, and suppose that near `K` the difference `σ₁ - σ₀ = dβ` is exact, for a
smooth one-form `β` vanishing along `K` which need not be invariant, and that the path
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate along `K`. The **equivariant relative Moser
theorem** (`TauCeti.SmoothTwoForm.exists_equivariant_diffeomorph_fix_eventually_mpullback_eq`)
gives a diffeomorphism `Φ` of `M` which

* fixes every point of `K` and moves only the points of a compact set,
* pulls `σ₁` back to `σ₀` on a neighbourhood of `K`,
* has identity differential at each point of `K` along whose orbit `β` has zero first jet,
* and commutes with the action: `Φ (a • x) = a • Φ x`.

The proof makes every ingredient of Moser's argument invariant. The primitive is replaced by its
average `β' = ∫ a^* β da` over the normalized Haar measure
(`TauCeti.SmoothForm.measureAverage`), which is invariant, still vanishes along the invariant set
`K`, keeps a zero first jet at a point when `β` has one along its orbit, and still satisfies
`dβ' = σ₁ - σ₀` on the largest invariant open subset of the region where `dβ = σ₁ - σ₀`, since
averaging commutes with `d` and fixes the invariant form `σ₁ - σ₀`. The Moser field is cut off
by an invariant function
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem`). The diffeomorphism given by
Moser's theorem with a given primitive and cut-off
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff`) commutes with
every diffeomorphism preserving these data, in particular with every element of `G`.

Now let `f : Q → M` be a compact embedded submanifold with invariant image, such as a compact
submanifold of fixed points, and let `M` be second countable. If `σ₀` and `σ₁` agree, as bilinear
forms on the full tangent spaces of `M`, at every point of `f(Q)`, and `σ₀` is nondegenerate
there, the **equivariant relative Moser theorem along a submanifold**
(`TauCeti.SmoothTwoForm.exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq`)
gives a diffeomorphism `Φ` as above which fixes `f(Q)` pointwise, with identity differential at
every point of `f(Q)`, and pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. If only the
pullbacks of `σ₀` and `σ₁` to `Q` agree, but the path `σ₀ + s (σ₁ - σ₀)` is nondegenerate along
`f(Q)`, the same holds except that the differential of `Φ` is the identity only at the points where
the two forms agree on the full ambient tangent space
(`exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq`).
So an invariant symplectic form near such a submanifold is determined, up to an equivariant
diffeomorphism fixing the submanifold, by its values along it: it can be compared with any
invariant closed form agreeing with it there, for instance a model form on an equivariant tubular
neighbourhood of a compact submanifold of fixed points.

The primitive comes from the relative Poincaré lemma
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`), on a tubular neighbourhood `W`
of `f(Q)` which need not be invariant. Moser's argument therefore runs on the largest invariant open
subset `{x | ∀ a, a • x ∈ W}` of `W` (`TopologicalSpace.Opens.invariantCore`), open since `G` is
compact, which still contains `f(Q)` and on which `G` still acts smoothly. The resulting compactly
supported equivariant diffeomorphism of that open subset extends by the identity to an equivariant
diffeomorphism of `M`.

Equivariant relative Moser theorems are the input of the equivariant normal forms of Hamiltonian
group actions: near a fixed point (equivariant Darboux), along a submanifold of fixed points, and
along an orbit (the Marle–Guillemin–Sternberg local model).

## Main results

* `TauCeti.SmoothTwoForm.exists_equivariant_diffeomorph_fix_eventually_mpullback_eq`: the
  equivariant relative Moser theorem along an invariant compact set, with a given primitive.
* `exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq`:
  the equivariant relative Moser theorem for invariant closed two-forms with equal pullbacks to a
  compact embedded submanifold with invariant image, joined by a path nondegenerate along it.
* `TauCeti.SmoothTwoForm.exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq`:
  the equivariant relative Moser theorem for invariant closed two-forms agreeing along such a
  submanifold, with identity differential along it.

## References

* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 22 (equivariant Moser and Darboux theorems).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 7.4 and Homework 21.
-/

public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [ChartedSpace HG G] [IsManifold IG ∞ G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

variable (G IG) in
include IG in
/-- **The equivariant relative Moser theorem.** Let a compact Lie group `G` act smoothly on a
boundaryless Hausdorff manifold, preserving closed two-forms `σ₀` and `σ₁`. Let `K` be an invariant
compact set and `β` a smooth one-form, vanishing along `K`, with `dβ = σ₁ - σ₀` on an open
neighbourhood `U` of `K`, and suppose the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate
along `K`. Then there is a diffeomorphism `Φ` which commutes with the action, fixes every point of
`K`, moves only the points of a compact set and pulls `σ₁` back to `σ₀` on a neighbourhood of `K`.
At each point of `K` along whose orbit `β` has zero first jet, the differential of `Φ` is the
identity. -/
theorem exists_equivariant_diffeomorph_fix_eventually_mpullback_eq {σ₀ σ₁ : SmoothTwoForm I M}
    (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hG₀ : ∀ a : G, mpullback I I (a • ·) σ₀.val = σ₀.val)
    (hG₁ : ∀ a : G, mpullback I I (a • ·) σ₁.val = σ₁.val)
    {β : SmoothForm I M ℝ 1} {U : Set M} (hU : IsOpen U)
    (hβ : ∀ x ∈ U, mextDeriv β.val x = (σ₁ - σ₀).val x)
    {K : Set M} (hK : IsCompact K) (hKG : ∀ (a : G), ∀ x ∈ K, a • x ∈ K) (hKU : K ⊆ U)
    (hβK : ∀ x ∈ K, β.val x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ K, (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ x ∈ K, (∀ a : G, HasFDerivAt (RoughForm.inChartAt β.val (a • x))
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (extChartAt I (a • x) (a • x))) →
        mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ∀ (a : G) (x : M), Φ (a • x) = a • Φ x := by
  borelize G
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  set μ := TauCeti.haarProb G
  set β' := SmoothForm.measureAverage IG μ β
  -- On the largest invariant open subset of `U`, the average primitive still has
  -- `dβ' = σ₁ - σ₀`: averaging commutes with `d` and fixes the invariant form `σ₁ - σ₀`.
  set U' := {x : M | ∀ a : G, a • x ∈ U}
  have hdβ' (x : M) (hx : x ∈ U') : mextDeriv β'.val x = (σ₁ - σ₀).val x := by
    have h := congrArg (fun α : SmoothForm I M ℝ 2 ↦ α.val x)
      (SmoothForm.mextDerivₗ_measureAverage IG μ β)
    simp only [mextDerivₗ_apply] at h
    rw [h]
    ext v
    have hpull (a : G) : (mextDeriv β.val) (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) =
        (σ₁ - σ₀).val x v := by
      rw [hβ _ (hx a), ← mpullback_apply, AddSubgroupClass.coe_sub, mpullback_sub, hG₀, hG₁]
    simp [SmoothForm.measureAverage_apply, mextDerivₗ_apply, hpull]
  -- An invariant cut-off supported where `dβ' = σ₁ - σ₀` and the path is nondegenerate.
  obtain ⟨N, hN, hKN, hndN⟩ := exists_isOpen_forall_nondegenerate hK hnd
  obtain ⟨ρ, hρ, hρ1, hρc, hρW, -, hρG⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem I IG
      ((TauCeti.isOpen_setOf_forall_smul_mem (G := G) hU).inter hN)
      (fun x hx ↦ ⟨fun a ↦ hKU (hKG a x hx), hKN hx⟩) hKG
  obtain ⟨Φ, hΦK, hΦρ, hΦ, hΦ1, hΦG⟩ := exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff
    h₀ h₁ hρ hρc (fun x hx ↦ hdβ' x (hρW hx).1) (fun x hx ↦ hndN x (hρW hx).2) hK
    (fun x hx ↦ SmoothForm.measureAverage_eq_zero_of_forall_smul IG μ β fun a ↦
      hβK _ (hKG a x hx)) hρ1
  refine ⟨Φ, hΦK, ⟨tsupport ρ, hρc, hΦρ⟩, hΦ, fun x hx hjet ↦ hΦ1 x hx ?_, fun a x ↦
    hΦG (Diffeomorph.smul IG I ∞ a) (hG₀ a) (hG₁ a)
      (SmoothForm.mpullback_smul_measureAverage IG μ β a) (hρG a) x⟩
  -- Averaging keeps a zero first jet along the orbit.
  exact SmoothForm.hasFDerivAt_inChartAt_measureAverage_of_forall_smul IG μ β
    (fun a ↦ hβK _ (hKG a x hx)) hjet

variable (G IG) in
include IG in
/-- Moser's argument on the largest invariant open subset `U` of an open set `W`, with a primitive
defined only on `U`: the compactly supported equivariant diffeomorphism of `U` given by the
equivariant relative Moser theorem extends by the identity to an equivariant diffeomorphism of
`M`. -/
private theorem exists_equivariant_diffeomorph_of_opens [ContinuousSMul G M] (W : Opens M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hG₀ : ∀ a : G, mpullback I I (a • ·) σ₀.val = σ₀.val)
    (hG₁ : ∀ a : G, mpullback I I (a • ·) σ₁.val = σ₁.val)
    {β : SmoothForm I (W.invariantCore G) ℝ 1}
    (hβ : mextDeriv β.val = mpullback I I (Subtype.val : W.invariantCore G → M) (σ₁ - σ₀).val)
    {K : Set (W.invariantCore G)} (hK : IsCompact K) (hKG : ∀ (a : G), ∀ x ∈ K, a • x ∈ K)
    (hβK : ∀ x ∈ K, β.val x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (x : M)).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ (Subtype.val '' K),
        (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ x ∈ K, (∀ a : G, HasFDerivAt (RoughForm.inChartAt β.val (a • x))
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (extChartAt I (a • x) (a • x))) →
        mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I (x : M))) ∧
      ∀ (a : G) (x : M), Φ (a • x) = a • Φ x := by
  let U := W.invariantCore G
  let res := SmoothForm.mpullback (I := I) (I' := I) (F := ℝ) (k := 2) (Subtype.val : U → M)
    contMDiff_subtypeVal
  have hval : MDifferentiable I I (Subtype.val : U → M) :=
    (contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero
  -- The restrictions of invariant forms to `U` are invariant.
  have hres (σ : SmoothTwoForm I M) (hσ : ∀ a : G, mpullback I I (a • ·) σ.val = σ.val) (a : G) :
      mpullback I I (a • ·) (res σ).val = (res σ).val := by
    have hcomp : (Subtype.val : U → M) ∘ (a • ·) = (a • ·) ∘ Subtype.val :=
      funext (Opens.coe_smul_invariantCore W a)
    have hdM : MDifferentiable I I fun x : M ↦ a • x :=
      ContMDiffSMul.mdifferentiable_const_smul (I := IG) (n := ∞) (by simp) a
    have hdU : MDifferentiable I I fun x : U ↦ a • x :=
      ContMDiffSMul.mdifferentiable_const_smul (I := IG) (n := ∞) (by simp) a
    rw [SmoothForm.coe_mpullback, ← mpullback_comp hdU hval, hcomp, mpullback_comp hval hdM, hσ]
  obtain ⟨Ψ, hΨK, ⟨C, hC, hΨC⟩, hΨ, hΨ1, hΨG⟩ :=
    exists_equivariant_diffeomorph_fix_eventually_mpullback_eq G IG (σ₀ := res σ₀)
      (σ₁ := res σ₁) (h₀.mpullback _ _) (h₁.mpullback _ _) (hres σ₀ hG₀) (hres σ₁ hG₁)
      isOpen_univ (fun x _ ↦ by rw [← map_sub, SmoothForm.coe_mpullback, hβ]) hK hKG
      (subset_univ _) hβK fun x hx s hs ↦ by
        rw [← map_sub, ← map_smul, ← map_add]
        exact (nondegenerate_bilinFormAt_mpullback_subtype_val_iff x).2 (hnd x hx s hs)
  -- Extend the compactly supported diffeomorphism of `U` by the identity.
  obtain ⟨Φ, hΦU, hΦC⟩ := Ψ.exists_extend_of_isCompact hC hΨC
  have hcomp : ⇑Φ ∘ (Subtype.val : U → M) = Subtype.val ∘ ⇑Ψ := funext hΦU
  refine ⟨Φ, fun x hx ↦ (hΦU x).trans (congrArg Subtype.val (hΨK x hx)),
    ⟨Subtype.val '' C, hC.image continuous_subtypeVal, hΦC⟩,
    SmoothForm.eventually_mpullback_eq_of_subtype_val_comp_eq Φ.contMDiff Ψ.contMDiff hcomp hΨ,
    fun x hx hjet ↦ (Manifold.mfderiv_eq_id_iff_of_comp_subtype_val hcomp.symm).1 (hΨ1 x hx hjet),
    fun a x ↦ ?_⟩
  -- `Φ` is `Ψ` on the invariant set `U` and the identity off it.
  by_cases hx : x ∈ U
  · rw [← Opens.coe_smul_invariantCore W a ⟨x, hx⟩, hΦU, hΨG, Opens.coe_smul_invariantCore,
      ← hΦU ⟨x, hx⟩]
  · have hnot {y : M} (hy : y ∉ U) : y ∉ Subtype.val '' C := by
      rintro ⟨z, -, rfl⟩
      exact hy z.property
    have hax : a • x ∉ U := fun h ↦ hx (by
      simpa only [inv_smul_smul] using Opens.smul_mem_invariantCore h a⁻¹)
    rw [hΦC _ (hnot hax), hΦC _ (hnot hx)]

variable [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

variable (G IG) in
include IG in
/-- **The equivariant relative Moser theorem for forms with equal pullbacks.** Let a compact Lie
group `G` act smoothly on a boundaryless second-countable Hausdorff manifold `M`, preserving closed
two-forms `σ₀` and `σ₁`, and let `f : Q → M` be a compact embedded submanifold whose image is
invariant, such as a compact submanifold of fixed points. Suppose that the pullbacks of `σ₀` and
`σ₁` along `f` agree and that the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate at every
point of `f(Q)`. Then there is a diffeomorphism `Φ` of `M` which commutes with the action, fixes
every point of `f(Q)`, moves only the points of a compact set, and pulls `σ₁` back to `σ₀` on a
neighbourhood of `f(Q)`. Moreover `Φ` fixes to first order every point `f q` at which `σ₁` and `σ₀`
agree as bilinear forms on the full ambient tangent space: its differential there is the
identity. -/
theorem exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq
    (f : SmoothEmbedding J I ∞ Q M) (hfG : ∀ (a : G) (q : Q), a • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hG₀ : ∀ a : G, mpullback I I (a • ·) σ₀.val = σ₀.val)
    (hG₁ : ∀ a : G, mpullback I I (a • ·) σ₁.val = σ₁.val)
    (hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ q, σ₁.val (f q) = σ₀.val (f q) →
        mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q))) ∧
      ∀ (a : G) (x : M), Φ (a • x) = a • Φ x := by
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  -- A primitive of `σ₁ - σ₀` on a neighbourhood `W` of `f(Q)`, vanishing along `f(Q)`, with zero
  -- first jet wherever `σ₁ - σ₀` vanishes.
  obtain ⟨W, hfW, βW, hβW, hdβW, hβW0, hβW1⟩ :=
    exists_relative_primitive_sub_of_mpullback_eq f h₀ h₁ hf
  -- Moser's argument runs on the largest invariant open subset `W'` of `W`, which still contains
  -- the invariant set `f(Q)`, with the restricted action and primitive.
  let W' := W.invariantCore G
  have hW'W : W' ≤ W := Opens.invariantCore_le G W
  let β : SmoothForm I W' ℝ 1 :=
    ⟨mpullback I I (Opens.inclusion hW'W) βW,
      (hβW.mpullback (contMDiff_inclusion hW'W)).mem_smoothBundleForms⟩
  have hβval : β.val = mpullback I I (Opens.inclusion hW'W) βW := rfl
  let g : Q → W' := fun q ↦
    ⟨f q, Opens.mem_invariantCore.2 fun a ↦ (hfG a q).choose_spec ▸ hfW (mem_range_self _)⟩
  have hgG (a : G) (q : Q) : a • g q = g (hfG a q).choose := Subtype.ext (hfG a q).choose_spec.symm
  obtain ⟨Φ, hΦK, hΦC, hΦ, hΦ1, hΦG⟩ := exists_equivariant_diffeomorph_of_opens G IG W h₀ h₁ hG₀ hG₁
    (β := β) (K := range g)
    (by
      rw [hβval, ← mpullback_inclusion_mextDeriv, hdβW,
        ← mpullback_comp ((contMDiff_inclusion (n := 1) hW'W).mdifferentiable one_ne_zero)
          ((contMDiff_subtypeVal (n := 1)).mdifferentiable one_ne_zero)]
      -- The inclusion of `W'` into `M` is the inclusion into `W` followed by that of `W`.
      rfl)
    (isCompact_range (f.contMDiff.continuous.subtype_mk fun q ↦ (g q).property))
    (by rintro a _ ⟨q, rfl⟩; exact ⟨_, (hgG a q).symm⟩)
    (by rintro _ ⟨q, rfl⟩; rw [hβval, mpullback_inclusion_apply]; exact hβW0 q)
    (by rintro _ ⟨q, rfl⟩; exact hnd q)
  refine ⟨Φ, fun q ↦ hΦK _ (mem_range_self q), hΦC, (range_comp Subtype.val g) ▸ hΦ,
    fun q hq ↦ hΦ1 _ (mem_range_self q) fun a ↦ ?_, hΦG⟩
  -- The primitive has zero first jet along the orbit of `f q`: `σ₁ - σ₀` vanishes at `f q`, hence
  -- at every point of its orbit, by invariance.
  have hη : (σ₁ - σ₀).val (f (hfG a q).choose) = 0 := by
    rw [(hfG a q).choose_spec]
    refine RoughForm.apply_smul_eq_zero_of_mpullback_inv_smul_eq ?_ ?_
    · rw [AddSubgroupClass.coe_sub, mpullback_sub, hG₀, hG₁]
    · rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hq, sub_self]
  rw [hgG, hβval, ← hasFDerivWithinAt_univ, ← ModelWithCorners.range_eq_univ I]
  exact hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero
    (contMDiff_inclusion hW'W).contMDiffAt (hβW0 _) (hβW1 _ hη).hasFDerivWithinAt

variable (G IG) in
include IG in
/-- **The equivariant relative Moser theorem along a submanifold.** Let a compact Lie group `G`
act smoothly on a boundaryless second-countable Hausdorff manifold `M`, preserving closed
two-forms `σ₀` and `σ₁`, and let `f : Q → M` be a compact embedded submanifold whose image is
invariant, such as a compact submanifold of fixed points. Suppose that `σ₀` and `σ₁` agree, as
bilinear forms on the full tangent spaces of `M`, at every point of `f(Q)`, and that `σ₀` is
nondegenerate along it. Then there is a diffeomorphism `Φ` of `M` which commutes with the action,
fixes every point of `f(Q)`, moves only the points of a compact set and pulls `σ₁` back to `σ₀`
on a neighbourhood of `f(Q)`. Its differential at every point of `f(Q)` is the identity of the
full ambient tangent space. -/
theorem exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq
    (f : SmoothEmbedding J I ∞ Q M) (hfG : ∀ (a : G) (q : Q), a • f q ∈ range f)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hG₀ : ∀ a : G, mpullback I I (a • ·) σ₀.val = σ₀.val)
    (hG₁ : ∀ a : G, mpullback I I (a • ·) σ₁.val = σ₁.val)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate) (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ q, mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q))) ∧
      ∀ (a : G) (x : M), Φ (a • x) = a • Φ x := by
  -- The forms agree along `f(Q)`, so do their pullbacks, and the path is constantly `σ₀` there.
  obtain ⟨Φ, hΦf, hΦC, hΦ, hΦ1, hΦG⟩ :=
    exists_equivariant_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq G IG f hfG
      h₀ h₁ hG₀ hG₁ (SmoothForm.mpullback_eq_of_forall_apply_eq f.contMDiff heq)
      fun q s _ ↦ bilinFormAt_add_smul_sub_of_eq (heq q) s ▸ hnd q
  exact ⟨Φ, hΦf, hΦC, hΦ, fun q ↦ hΦ1 q (heq q), hΦG⟩

end TauCeti.SmoothTwoForm

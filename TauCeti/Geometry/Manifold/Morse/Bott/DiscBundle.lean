/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
import TauCeti.Topology.FiberBundle.Separation

/-!
# Attaching the negative disc bundle of a compact Morse–Bott submanifold

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, with critical value `c`, and suppose that the band `f⁻¹[c - δ, c + δ]` is
compact and that all its critical points lie on `S`. A fibre metric `g` on the normal bundle `ν`
of `i` splits it into the negative and positive normal bundles `ν⁻` and `ν⁺`, on which the normal
Hessian `Hess` is negative, respectively positive, definite
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`). This file proves that
crossing the critical level attaches the **negative disc bundle**
`D_ε = {v ∈ ν⁻ | -½ Hess (v, v) ≤ ε}`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in the
namespace `TauCeti.SmoothEmbedding`): there is a partial diffeomorphism `Θ` from the total space
of `ν` to `M` along the zero section, sending the zero section to `i`, with `f ∘ Θ = c + ½ Hess`,
and for all small `ε > 0` the sublevel `{f ≤ c + ε}` strong deformation retracts onto
`{f ≤ c - ε} ∪ Θ(D_ε)`. So up to homotopy relative
to `{f ≤ c - ε}`, crossing the level `c` attaches the disc bundle of `ν⁻` along its sphere bundle.
When `S` is a point, `D_ε` is a closed ball in the negative eigenspace of the Hessian, and this is
Milnor's attachment of a cell.

The theorem holds for any smooth vector bundle `V` over a compact Hausdorff manifold carrying such
a quadratic normal form (`TauCeti.exists_sublevel_union_image_negativeDiscBundle_deformation`):
`V = Vn ⊕ Vp` with smooth projection onto `Vn`, a fibrewise symmetric form `Q` which is negative
definite on `Vn`, positive definite on `Vp`, and for which `Vn` and `Vp` are orthogonal, and a
smooth partial diffeomorphism `Θ` along the zero section with `f ∘ Θ = c + ½ Q`. The Morse–Bott
case takes for `Θ` the Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`) and for
`Vn`, `Vp` the negative and positive normal spaces, whose projection is smooth
(`IsNondegenerateCriticalSubmanifold.contMDiff_projection_negativeNormalSpace`), both in the
namespace `TauCeti.SmoothEmbedding`.

The general statement is reduced to the attachment theorem for a tube on `M`,
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`. Writing `w = u + v` with `u ∈ Vn`
and `v ∈ Vp`, the tube is the image under `Θ` of the vectors `w` all of whose rescalings
`a u + b v`, `a, b ∈ [0, 1]`, lie in the source of `Θ`, with `s = -½ Q (u, u)` and
`t = ½ Q (v, v)`, and the scaling of the positive directions is `(τ, u + v) ↦ u + τ v`. The part
`{s + 2t ≤ 2ε}` of the tube is compact for small `ε` because the base is compact: `s + 2t` has a
positive lower bound on the boundary of a compact neighbourhood of the zero section, and it is
multiplied by `l²` along the radial path `l ↦ l • w`.

## Main results

* `TauCeti.exists_sublevel_union_image_negativeDiscBundle_deformation`: attaching the negative
  disc bundle of a quadratic normal form on a vector bundle over a compact base.
* `IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in
  the namespace `TauCeti.SmoothEmbedding`: crossing the critical level of a compact Morse–Bott
  submanifold attaches its negative disc bundle.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
-/

public section

noncomputable section

open Bundle Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Scaling the two components of a split vector bundle -/

section Scale

variable {B F : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  {Vn Vp : ∀ b, Submodule ℝ (V b)} (hV : ∀ b, IsCompl (Vn b) (Vp b))

/-- The component of a vector in the first summand of the splitting `V = Vn ⊕ Vp`. -/
private def negPart (w : TotalSpace F V) : V w.proj :=
  (Vn w.proj).projection (Vp w.proj) (hV w.proj) w.2

/-- The component of a vector in the second summand of the splitting `V = Vn ⊕ Vp`. -/
private def posPart (w : TotalSpace F V) : V w.proj :=
  (Vp w.proj).projection (Vn w.proj) (hV w.proj).symm w.2

/-- Scaling the two components of a vector by `a` and `b`. -/
private def scale (a b : ℝ) (w : TotalSpace F V) : TotalSpace F V :=
  ⟨w.proj, a • negPart hV w + b • posPart hV w⟩

private theorem scale_def (a b : ℝ) (w : TotalSpace F V) :
    scale hV a b w = ⟨w.proj, a • negPart hV w + b • posPart hV w⟩ :=
  rfl

private theorem negPart_mk (b : B) (v : V b) :
    negPart (F := F) hV ⟨b, v⟩ = (Vn b).projection (Vp b) (hV b) v :=
  rfl

private theorem posPart_mk (b : B) (v : V b) :
    posPart (F := F) hV ⟨b, v⟩ = (Vp b).projection (Vn b) (hV b).symm v :=
  rfl

private theorem negPart_mem (w : TotalSpace F V) : negPart hV w ∈ Vn w.proj :=
  Submodule.projection_apply_mem _ _

private theorem posPart_mem (w : TotalSpace F V) : posPart hV w ∈ Vp w.proj :=
  Submodule.projection_apply_mem _ _

private theorem negPart_add_posPart (w : TotalSpace F V) :
    negPart hV w + posPart hV w = w.2 :=
  Submodule.projection_add_projection_eq_self _ _

private theorem negPart_scale (a b : ℝ) (w : TotalSpace F V) :
    negPart hV (scale hV a b w) = a • negPart hV w := by
  refine (negPart_mk hV w.proj (a • negPart hV w + b • posPart hV w)).trans ?_
  rw [map_add, map_smul, map_smul,
    Submodule.projection_apply_of_mem_left _ (negPart_mem hV w),
    (Submodule.projection_apply_eq_zero_iff _).2 (posPart_mem hV w), smul_zero, add_zero]

private theorem posPart_scale (a b : ℝ) (w : TotalSpace F V) :
    posPart hV (scale hV a b w) = b • posPart hV w := by
  refine (posPart_mk hV w.proj (a • negPart hV w + b • posPart hV w)).trans ?_
  rw [map_add, map_smul, map_smul,
    Submodule.projection_apply_of_mem_left _ (posPart_mem hV w),
    (Submodule.projection_apply_eq_zero_iff _).2 (negPart_mem hV w), smul_zero, zero_add]

private theorem scale_one_one (w : TotalSpace F V) : scale hV 1 1 w = w := by
  simp [scale, negPart_add_posPart]

private theorem scale_scale (a b a' b' : ℝ) (w : TotalSpace F V) :
    scale hV a b (scale hV a' b' w) = scale hV (a * a') (b * b') w := by
  rw [scale_def, negPart_scale, posPart_scale, scale_def (a := a * a'), mul_smul, mul_smul]
  rfl

private theorem scale_zeroSection (a b : ℝ) (x : B) :
    scale hV a b (zeroSection F V x) = zeroSection F V x := by
  have hn : negPart hV (zeroSection F V x) = 0 := (negPart_mk hV x 0).trans (map_zero _)
  have hp : posPart hV (zeroSection F V x) = 0 := (posPart_mk hV x 0).trans (map_zero _)
  rw [scale_def, hn, hp, smul_zero, smul_zero, add_zero]
  rfl

private theorem scale_zero_zero (w : TotalSpace F V) :
    scale hV 0 0 w = zeroSection F V w.proj := by
  rw [scale_def, zero_smul, zero_smul, add_zero]
  rfl

private theorem scale_eq_self_of_posPart_eq_zero {w : TotalSpace F V}
    (hw : posPart hV w = 0) (b : ℝ) : scale hV 1 b w = w := by
  conv_rhs => rw [← scale_one_one hV w]
  simp [scale, hw]

variable (Q : ∀ b, LinearMap.BilinForm ℝ (V b))

/-- Minus half the form on the `Vn`-component, `s = -½ Q (u, u)`. -/
private def negSq (w : TotalSpace F V) : ℝ :=
  -(2⁻¹ * Q w.proj (negPart hV w) (negPart hV w))

/-- Half the form on the `Vp`-component, `t = ½ Q (v, v)`. -/
private def posSq (w : TotalSpace F V) : ℝ :=
  2⁻¹ * Q w.proj (posPart hV w) (posPart hV w)

private theorem negSq_scale (a b : ℝ) (w : TotalSpace F V) :
    negSq hV Q (scale hV a b w) = a ^ 2 * negSq hV Q w := by
  -- The base point of `scale hV a b w` is `w.proj` by definition.
  change -(2⁻¹ * Q w.proj (negPart hV (scale hV a b w)) (negPart hV (scale hV a b w))) = _
  rw [negSq, negPart_scale]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem posSq_scale (a b : ℝ) (w : TotalSpace F V) :
    posSq hV Q (scale hV a b w) = b ^ 2 * posSq hV Q w := by
  -- The base point of `scale hV a b w` is `w.proj` by definition.
  change 2⁻¹ * Q w.proj (posPart hV (scale hV a b w)) (posPart hV (scale hV a b w)) = _
  rw [posSq, posPart_scale]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- For a symmetric form for which the two summands are orthogonal, half the form is `t - s`. -/
private theorem half_apply_self (hQ : ∀ b, (Q b).IsSymm)
    (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0) (w : TotalSpace F V) :
    2⁻¹ * Q w.proj w.2 w.2 = -negSq hV Q w + posSq hV Q w := by
  have h1 := hQnp _ _ (negPart_mem hV w) _ (posPart_mem hV w)
  have h2 : Q w.proj (posPart hV w) (negPart hV w) = 0 := by
    rw [← LinearMap.BilinForm.IsSymm.eq (hQ w.proj), h1]
  rw [negSq, posSq, ← negPart_add_posPart hV w]
  simp only [map_add, LinearMap.add_apply, h1, h2]
  ring

private theorem negSq_nonneg (hQn : ∀ b, ∀ v ∈ Vn b, v ≠ 0 → Q b v v < 0)
    (w : TotalSpace F V) : 0 ≤ negSq hV Q w := by
  by_cases h : negPart hV w = 0
  · simp [negSq, h]
  · have := hQn _ _ (negPart_mem hV w) h
    rw [negSq]
    linarith

private theorem posSq_nonneg (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v)
    (w : TotalSpace F V) : 0 ≤ posSq hV Q w := by
  by_cases h : posPart hV w = 0
  · simp [posSq, h]
  · have := hQp _ _ (posPart_mem hV w) h
    rw [posSq]
    linarith

private theorem negPart_eq_zero_of_negSq_eq_zero (hQn : ∀ b, ∀ v ∈ Vn b, v ≠ 0 → Q b v v < 0)
    {w : TotalSpace F V} (hw : negSq hV Q w = 0) : negPart hV w = 0 := by
  by_contra h
  have := hQn _ _ (negPart_mem hV w) h
  rw [negSq] at hw
  linarith

private theorem posPart_eq_zero_of_posSq_eq_zero (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v)
    {w : TotalSpace F V} (hw : posSq hV Q w = 0) : posPart hV w = 0 := by
  by_contra h
  have := hQp _ _ (posPart_mem hV w) h
  rw [posSq] at hw
  linarith

/-- On the first summand, `t` vanishes. -/
private theorem posSq_eq_zero_of_mem {w : TotalSpace F V} (hw : w.2 ∈ Vn w.proj) :
    posSq hV Q w = 0 := by
  have hp : posPart hV w = 0 := (Submodule.projection_apply_eq_zero_iff _).2 hw
  simp [posSq, hp]

/-- On the first summand, `s` is minus half the form. -/
private theorem negSq_eq_of_mem (hQ : ∀ b, (Q b).IsSymm)
    (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0) {w : TotalSpace F V}
    (hw : w.2 ∈ Vn w.proj) : negSq hV Q w = -(2⁻¹ * Q w.proj w.2 w.2) := by
  rw [half_apply_self hV Q hQ hQnp, posSq_eq_zero_of_mem hV Q hw]
  ring

/-- A vector on which `s` and `t` both vanish lies on the zero section. -/
private theorem eq_zeroSection_of_negSq_add_posSq_eq_zero
    (hQn : ∀ b, ∀ v ∈ Vn b, v ≠ 0 → Q b v v < 0) (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v)
    {w : TotalSpace F V} (hw : negSq hV Q w + 2 * posSq hV Q w = 0) :
    w = zeroSection F V w.proj := by
  have hs := negSq_nonneg hV Q hQn w
  have ht := posSq_nonneg hV Q hQp w
  have hn := negPart_eq_zero_of_negSq_eq_zero hV Q hQn (by linarith : negSq hV Q w = 0)
  have hp := posPart_eq_zero_of_posSq_eq_zero hV Q hQp (by linarith : posSq hV Q w = 0)
  conv_lhs => rw [← scale_one_one hV w]
  rw [scale_def, hn, hp, smul_zero, add_zero]
  rfl

end Scale

section Smooth

variable {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)]
  [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V IB]
  {Vn Vp : ∀ b, Submodule ℝ (V b)} (hV : ∀ b, IsCompl (Vn b) (Vp b))

/-- If projecting onto the first summand is smooth, then scaling the two components is smooth,
jointly in the scalars and the vector. -/
private theorem contMDiff_scale
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V)) :
    ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod (IB.prod 𝓘(ℝ, F)))) (IB.prod 𝓘(ℝ, F)) ∞
      fun p : ℝ × ℝ × TotalSpace F V ↦ scale hV p.1 p.2.1 p.2.2 := by
  intro p₀
  have hw : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod (IB.prod 𝓘(ℝ, F)))) (IB.prod 𝓘(ℝ, F)) ∞
      fun p : ℝ × ℝ × TotalSpace F V ↦ p.2.2 := contMDiff_snd.comp contMDiff_snd
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨((Bundle.contMDiff_proj _).comp hw).contMDiffAt, ?_⟩
  set e := trivializationAt F V p₀.2.2.proj
  have hp₀ : p₀.2.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt F V _
  -- The fibre coordinates of `w` and of its first component are smooth near `p₀`.
  have he : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ (fun w ↦ (e w).2) p₀.2.2 :=
    ((e.contMDiffOn (IB := IB) (n := ∞)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source.mpr hp₀))).snd
  have hen : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
      (fun w ↦ (e ⟨w.proj, negPart hV w⟩).2) p₀.2.2 :=
    (((e.contMDiffOn (IB := IB) (n := ∞)).contMDiffAt
      (e.open_source.mem_nhds (e.mem_source (x := ⟨_, negPart hV p₀.2.2⟩)|>.mpr hp₀))).comp
        p₀.2.2 (hVs p₀.2.2)).snd
  refine ((contMDiff_fst.contMDiffAt.smul (hen.comp p₀ hw.contMDiffAt)).add
    ((contMDiff_fst.comp contMDiff_snd).contMDiffAt.smul
      ((he.comp p₀ hw.contMDiffAt).sub (hen.comp p₀ hw.contMDiffAt)))).congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj F V).continuousAt.comp hw.continuous.continuousAt
    |>.preimage_mem_nhds (e.open_baseSet.mem_nhds hp₀)] with p hp
  -- In the trivialization, the fibre coordinate is linear on the fibre over `p.2.2.proj`.
  have hp' : p.2.2.proj ∈ e.baseSet := hp
  have hlin (x : V p.2.2.proj) : (e ⟨p.2.2.proj, x⟩).2 = e.linearMapAt ℝ p.2.2.proj x := by
    rw [e.coe_linearMapAt_of_mem hp']
  have hpos : posPart hV p.2.2 = p.2.2.2 - negPart hV p.2.2 :=
    eq_sub_of_add_eq' (negPart_add_posPart hV p.2.2)
  -- Scaling does not move the base point.
  have he_eq : trivializationAt F V (scale hV p₀.1 p₀.2.1 p₀.2.2).proj = e := rfl
  simp only [he_eq, Pi.add_apply, Pi.smul_apply', Function.comp_apply]
  rw [scale_def, hlin, hlin, hpos, map_add,
    map_smul, map_smul, map_sub, ← hlin p.2.2.2]

end Smooth

/-! ### The tube and the radial path -/

section Tube

variable {B F : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)]
  {Vn Vp : ∀ b, Submodule ℝ (V b)} (hV : ∀ b, IsCompl (Vn b) (Vp b))

/-- If scaling is continuous, the vectors all of whose rescalings of the two components by
factors in `[0, 1]` lie in an open set form an open set. -/
private theorem isOpen_setOf_forall_scale_mem
    (hsc : Continuous fun p : ℝ × ℝ × TotalSpace F V ↦ scale hV p.1 p.2.1 p.2.2)
    {U : Set (TotalSpace F V)} (hU : IsOpen U) :
    IsOpen {w | ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, scale hV a b w ∈ U} := by
  refine isOpen_iff_eventually.2 fun w hw ↦ ?_
  have hc : Continuous fun z : TotalSpace F V × (ℝ × ℝ) ↦ scale hV z.2.1 z.2.2 z.1 :=
    hsc.comp (continuous_snd.fst.prodMk (continuous_snd.snd.prodMk continuous_fst))
  filter_upwards [(isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    (P := fun w (ab : ℝ × ℝ) ↦ scale hV ab.1 ab.2 w ∈ U) fun ab hab ↦
      hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hw _ hab.1 _ hab.2))]
    with w' hw' a ha b hb using hw' (a, b) ⟨ha, hb⟩

/-- **The radial path argument.** Let `N` be a closed set containing the zero section in its
interior, and let `q ≥ 0` be multiplied by `l²` when both components are scaled by `l`. If
`q ≥ m` on `N \ interior N`, then every vector with `q < m` lies in the interior of `N`: the
radial path from the zero section to it would otherwise meet `N \ interior N`. -/
private theorem mem_interior_of_lt
    (hsc : Continuous fun p : ℝ × ℝ × TotalSpace F V ↦ scale hV p.1 p.2.1 p.2.2)
    {N : Set (TotalSpace F V)} (hNc : IsClosed N)
    (hZN : ∀ x, zeroSection F V x ∈ interior N) {q : TotalSpace F V → ℝ} (hq0 : ∀ w, 0 ≤ q w)
    (hqscale : ∀ l w, q (scale hV l l w) = l ^ 2 * q w) {m : ℝ}
    (hmq : ∀ w ∈ N \ interior N, m ≤ q w) {w : TotalSpace F V} (hw : q w < m) :
    w ∈ interior N := by
  by_contra hwN
  let γ : ℝ → TotalSpace F V := fun l ↦ scale hV l l w
  have hγ : Continuous γ := hsc.comp (continuous_id.prodMk (continuous_id.prodMk continuous_const))
  by_cases hmeet : ∃ l ∈ Icc (0 : ℝ) 1, γ l ∈ N \ interior N
  · obtain ⟨l, hl, hlN⟩ := hmeet
    have h1 := hmq _ hlN
    rw [hqscale] at h1
    nlinarith [pow_le_one₀ hl.1 hl.2 (n := 2), hq0 w]
  · simp only [not_exists, not_and] at hmeet
    -- Otherwise the path, which starts in `interior N`, stays in `interior N`, by connectedness.
    have hsub : γ '' Icc 0 1 ⊆ interior N ∪ Nᶜ := by
      rintro _ ⟨l, hl, rfl⟩
      by_cases h : γ l ∈ N
      · exact Or.inl (by_contra fun h' ↦ hmeet l hl ⟨h, h'⟩)
      · exact Or.inr h
    have hγ0 : γ 0 = zeroSection F V w.proj := scale_zero_zero hV w
    have := (isPreconnected_Icc.image γ hγ.continuousOn).subset_left_of_subset_union
      isOpen_interior hNc.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hsub
      ⟨γ 0, mem_image_of_mem _ ⟨le_rfl, zero_le_one⟩, hγ0 ▸ hZN _⟩
    exact hwN (scale_one_one hV w ▸ this (mem_image_of_mem γ ⟨zero_le_one, le_rfl⟩))

end Tube

/-! ### The attachment theorem for a quadratic normal form on a vector bundle -/

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)]
  [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V]

section Tube

variable {Vn Vp : ∀ b, Submodule ℝ (V b)} (hV : ∀ b, IsCompl (Vn b) (Vp b))
  (Q : ∀ b, LinearMap.BilinForm ℝ (V b))
  (Θ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞)

/-- The tube of `Θ` in the total space: the vectors all of whose rescalings of the two components
by factors in `[0, 1]` lie in the source of `Θ`. -/
private def tube : Set (TotalSpace F V) :=
  {w | ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, scale hV a b w ∈ Θ.source}

private theorem tube_subset_source : tube hV Θ ⊆ Θ.source := fun w hw ↦
  scale_one_one hV w ▸ hw 1 ⟨zero_le_one, le_rfl⟩ 1 ⟨zero_le_one, le_rfl⟩

private theorem scale_mem_tube {w : TotalSpace F V} (hw : w ∈ tube hV Θ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : scale hV a b w ∈ tube hV Θ :=
  fun a' ha' b' hb' ↦ by
    rw [scale_scale]
    exact hw _ (unitInterval.mul_mem ha' ha) _ (unitInterval.mul_mem hb' hb)

private theorem zeroSection_mem_tube (hΘ₀ : ∀ b, zeroSection F V b ∈ Θ.source) (x : B) :
    zeroSection F V x ∈ tube hV Θ := fun a _ b _ ↦ by
  rw [scale_zeroSection]
  exact hΘ₀ x

private theorem left_inv_of_mem_tube {w : TotalSpace F V} (hw : w ∈ tube hV Θ) :
    Θ.symm (Θ w) = w :=
  Θ.left_inv (tube_subset_source hV Θ hw)

private theorem image_tube_subset_target : Θ '' tube hV Θ ⊆ Θ.target :=
  image_subset_iff.2 fun _ hw ↦ Θ.map_source (tube_subset_source hV Θ hw)

private theorem mapsTo_symm_image_tube : MapsTo Θ.symm (Θ '' tube hV Θ) (tube hV Θ) := by
  rintro _ ⟨w, hw, rfl⟩
  rwa [left_inv_of_mem_tube hV Θ hw]

variable {f : M → ℝ} {c : ℝ}

/-- The normal form of `f`, read on the two components. -/
private theorem apply_eq_sub_negSq_add_posSq (hQ : ∀ b, (Q b).IsSymm)
    (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0)
    (hΘf : ∀ w ∈ Θ.source, f (Θ w) = c + 2⁻¹ * Q w.proj w.2 w.2) {w : TotalSpace F V}
    (hw : w ∈ Θ.source) : f (Θ w) = c - negSq hV Q w + posSq hV Q w := by
  rw [hΘf w hw, half_apply_self hV Q hQ hQnp]
  ring

/-- The points of the image of the tube where `t = 0` and `s ≤ ε` are the image of the negative
disc bundle `D_ε`, once `D_ε` lies in the tube. -/
private theorem setOf_mem_image_tube_eq_image (hQ : ∀ b, (Q b).IsSymm)
    (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v)
    (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0) {ε : ℝ}
    (hDT : {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε} ⊆ tube hV Θ) :
    {x | x ∈ Θ '' tube hV Θ ∧ posSq hV Q (Θ.symm x) = 0 ∧ negSq hV Q (Θ.symm x) ≤ ε} =
      Θ '' {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε} := by
  ext x
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, htx, hsx⟩
    rw [left_inv_of_mem_tube hV Θ hw] at htx hsx
    have hwn : w.2 ∈ Vn w.proj := by
      rw [← negPart_add_posPart hV w, posPart_eq_zero_of_posSq_eq_zero hV Q hQp htx, add_zero]
      exact negPart_mem hV w
    exact ⟨w, ⟨hwn, negSq_eq_of_mem hV Q hQ hQnp hwn ▸ hsx⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨mem_image_of_mem _ (hDT hw), ?_, ?_⟩ <;> rw [left_inv_of_mem_tube hV Θ (hDT hw)]
    · exact posSq_eq_zero_of_mem hV Q hw.1
    · exact negSq_eq_of_mem hV Q hQ hQnp hw.1 ▸ hw.2

/-- If the vectors of the tube with `s + 2t ≤ 2ε` lie in a compact closed subset `N` of the tube,
then the part `{s + 2t ≤ 2ε}` of the image of the tube is compact. -/
private theorem isCompact_setOf_mem_image_tube {N : Set (TotalSpace F V)} (hN : IsCompact N)
    (hNc : IsClosed N) (hNT : N ⊆ tube hV Θ)
    (hqc : ContinuousOn (fun w ↦ negSq hV Q w + 2 * posSq hV Q w) (tube hV Θ)) {ε : ℝ}
    (hNq : ∀ w, negSq hV Q w + 2 * posSq hV Q w ≤ 2 * ε → w ∈ N) :
    IsCompact {x | x ∈ Θ '' tube hV Θ ∧
      negSq hV Q (Θ.symm x) + 2 * posSq hV Q (Θ.symm x) ≤ 2 * ε} := by
  have hKeq : {x | x ∈ Θ '' tube hV Θ ∧
      negSq hV Q (Θ.symm x) + 2 * posSq hV Q (Θ.symm x) ≤ 2 * ε} =
      Θ '' (N ∩ (fun w ↦ negSq hV Q w + 2 * posSq hV Q w) ⁻¹' Iic (2 * ε)) := by
    ext x
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hx⟩
      rw [left_inv_of_mem_tube hV Θ hw] at hx
      exact ⟨w, ⟨hNq w hx, hx⟩, rfl⟩
    · rintro ⟨w, ⟨hwN, hw⟩, rfl⟩
      refine ⟨mem_image_of_mem _ (hNT hwN), ?_⟩
      rw [left_inv_of_mem_tube hV Θ (hNT hwN)]
      exact hw
  rw [hKeq]
  exact (hN.of_isClosed_subset ((hqc.mono hNT).preimage_isClosed_of_isClosed hNc isClosed_Iic)
    inter_subset_left).image_of_continuousOn
      (Θ.contMDiffOn.continuousOn.mono (inter_subset_left.trans
        (hNT.trans (tube_subset_source hV Θ))))

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]

private theorem isOpen_tube
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V)) :
    IsOpen (tube hV Θ) :=
  isOpen_setOf_forall_scale_mem hV (contMDiff_scale hV hVs).continuous Θ.open_source

/-- On the tube, `s` and `t` are smooth: there they are read off from `f ∘ Θ` on the two
components, `s w = c - f (Θ u)` and `t w = f (Θ v) - c`. -/
private theorem contMDiffOn_negSq_posSq_tube (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V))
    (hQ : ∀ b, (Q b).IsSymm) (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0)
    (hΘf : ∀ w ∈ Θ.source, f (Θ w) = c + 2⁻¹ * Q w.proj w.2 w.2) :
    ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ (negSq hV Q) (tube hV Θ) ∧
      ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ (posSq hV Q) (tube hV Θ) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfΘ (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
      ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ (fun w ↦ f (Θ (scale hV a b w))) (tube hV Θ) :=
    hfs.comp_contMDiffOn (Θ.contMDiffOn.comp ((contMDiff_scale hV hVs).comp
      (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))).contMDiffOn
        fun w (hw : w ∈ tube hV Θ) ↦ hw a ha b hb)
  have h (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) {w : TotalSpace F V}
      (hw : w ∈ tube hV Θ) :
      f (Θ (scale hV a b w)) = c - a ^ 2 * negSq hV Q w + b ^ 2 * posSq hV Q w := by
    rw [apply_eq_sub_negSq_add_posSq hV Q Θ hQ hQnp hΘf (hw a ha b hb), negSq_scale, posSq_scale]
  have hn {w : TotalSpace F V} (hw : w ∈ tube hV Θ) :
      negSq hV Q w = c - f (Θ (scale hV 1 0 w)) := by
    rw [h 1 0 h11 h01 hw]
    ring
  have hp {w : TotalSpace F V} (hw : w ∈ tube hV Θ) :
      posSq hV Q w = f (Θ (scale hV 0 1 w)) - c := by
    rw [h 0 1 h01 h11 hw]
    ring
  exact ⟨(contMDiffOn_const.sub (hfΘ 1 0 h11 h01)).congr fun w hw ↦ hn hw,
    ((hfΘ 0 1 h01 h11).sub contMDiffOn_const).congr fun w hw ↦ hp hw⟩

/-- **The scaling of the positive directions** of the image of the tube: scaling the second
component of `Θ⁻¹ x` by `τ ∈ [0, 1]`. -/
private theorem exists_tubeScaling
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V)) :
    ∃ φ : C(unitInterval × (Θ '' tube hV Θ), Θ '' tube hV Θ),
      (∀ p, Θ.symm (φ p) = scale hV 1 p.1 (Θ.symm p.2)) ∧ (∀ x, φ (1, x) = x) ∧
      ∀ τ (x : Θ '' tube hV Θ), posPart hV (Θ.symm x) = 0 → φ (τ, x) = x := by
  have hWt := image_tube_subset_target hV Θ
  have hφT (p : unitInterval × (Θ '' tube hV Θ)) : scale hV 1 p.1 (Θ.symm p.2) ∈ tube hV Θ :=
    scale_mem_tube hV Θ (mapsTo_symm_image_tube hV Θ p.2.2) ⟨zero_le_one, le_rfl⟩ p.1.2
  have hsymmc : Continuous fun p : unitInterval × (Θ '' tube hV Θ) ↦ Θ.symm p.2 :=
    Θ.symm.contMDiffOn.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_snd)
      fun p ↦ hWt p.2.2
  refine ⟨{ toFun := fun p ↦ ⟨Θ (scale hV 1 p.1 (Θ.symm p.2)), mem_image_of_mem _ (hφT p)⟩
            continuous_toFun := (Θ.contMDiffOn.continuousOn.comp_continuous
              ((contMDiff_scale hV hVs).continuous.comp (continuous_const.prodMk
                ((continuous_subtype_val.comp continuous_fst).prodMk hsymmc)))
              fun p ↦ tube_subset_source hV Θ (hφT p)).subtype_mk _ },
    fun p ↦ left_inv_of_mem_tube hV Θ (hφT p), fun x ↦ ?_, fun τ x hx ↦ ?_⟩
  · exact Subtype.ext ((congrArg Θ (scale_one_one hV _)).trans (Θ.right_inv (hWt x.2)))
  · exact Subtype.ext ((congrArg Θ (scale_eq_self_of_posPart_eq_zero hV hx _)).trans
      (Θ.right_inv (hWt x.2)))

end Tube

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]

/-- At a point `Θ w` of the image of a tube on which `s ∘ Θ = -½ Q(u, u)` and
`t ∘ Θ = ½ Q(v, v)`, where `t` does not vanish, scaling the second component of `w` gives a
tangent vector killed by `ds` but not by `dt`. -/
private theorem exists_mfderiv_eq_zero_and_ne_zero {Vn Vp : ∀ b, Submodule ℝ (V b)}
    (hV : ∀ b, IsCompl (Vn b) (Vp b))
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V))
    (Q : ∀ b, LinearMap.BilinForm ℝ (V b))
    (Θ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞) {T : Set (TotalSpace F V)}
    (hTo : IsOpen T) (hTU : T ⊆ Θ.source) {s t : M → ℝ}
    (hsΘ : ∀ w ∈ T, s (Θ w) = negSq hV Q w) (htΘ : ∀ w ∈ T, t (Θ w) = posSq hV Q w)
    {w : TotalSpace F V} (hw : w ∈ T) (hsd : MDifferentiableAt I 𝓘(ℝ) s (Θ w))
    (htd : MDifferentiableAt I 𝓘(ℝ) t (Θ w)) (htw : posSq hV Q w ≠ 0) :
    ∃ v : TangentSpace I (Θ w), mfderiv I 𝓘(ℝ) s (Θ w) v = 0 ∧ mfderiv I 𝓘(ℝ) t (Θ w) v ≠ 0 := by
  let γ : ℝ → TotalSpace F V := fun l ↦ scale hV 1 l w
  have hγ : ContMDiff 𝓘(ℝ) (IB.prod 𝓘(ℝ, F)) ∞ γ :=
    (contMDiff_scale hV hVs).comp (contMDiff_const.prodMk (contMDiff_id.prodMk contMDiff_const))
  have hγ1 : γ 1 = w := scale_one_one hV w
  have hev : ∀ᶠ l in 𝓝 (1 : ℝ), γ l ∈ T :=
    hγ.continuous.continuousAt.preimage_mem_nhds (hTo.mem_nhds (hγ1 ▸ hw))
  have hΘγ : MDifferentiableAt 𝓘(ℝ) I (Θ ∘ γ) 1 :=
    (Θ.mdifferentiableAt (by simp) (hTU (hγ1 ▸ hw))).comp 1 (hγ.mdifferentiableAt (by simp))
  have hx : (Θ ∘ γ) 1 = Θ w := congrArg Θ hγ1
  rw [← hx] at hsd htd ⊢
  refine ⟨mfderiv 𝓘(ℝ) I (Θ ∘ γ) 1 (1 : ℝ), ?_, ?_⟩
  · -- Along `γ`, `s` is constant.
    have hsγ : s ∘ (Θ ∘ γ) =ᶠ[𝓝 1] fun _ ↦ negSq hV Q w := by
      filter_upwards [hev] with l hl
      rw [comp_apply, comp_apply, hsΘ _ hl, negSq_scale, one_pow, one_mul]
    have hc := mfderiv_comp (1 : ℝ) hsd hΘγ
    rw [hsγ.mfderiv_eq, mfderiv_const] at hc
    exact (DFunLike.congr_fun hc (1 : ℝ)).symm
  · -- Along `γ`, `t` is `l ↦ l² t`, with derivative `2t ≠ 0` at `l = 1`.
    have htγ : t ∘ (Θ ∘ γ) =ᶠ[𝓝 1] fun l ↦ l ^ 2 * posSq hV Q w := by
      filter_upwards [hev] with l hl
      rw [comp_apply, comp_apply, htΘ _ hl, posSq_scale]
    have hc := mfderiv_comp (1 : ℝ) htd hΘγ
    rw [htγ.mfderiv_eq, mfderiv_eq_fderiv] at hc
    have hd : HasDerivAt (fun l : ℝ ↦ l ^ 2 * posSq hV Q w) (2 * posSq hV Q w) 1 := by
      simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const (posSq hV Q w)
    -- The tangent spaces of `ℝ` are `ℝ` itself, so the identifications in `hc` are identities.
    have h1 : fderiv ℝ (fun l : ℝ ↦ l ^ 2 * posSq hV Q w) 1 1 =
        mfderiv I 𝓘(ℝ) t ((Θ ∘ γ) 1) (mfderiv 𝓘(ℝ) I (Θ ∘ γ) 1 (1 : ℝ)) :=
      DFunLike.congr_fun hc (1 : ℝ)
    intro h0
    have h2 := h1.trans h0
    rw [fderiv_apply_one_eq_deriv, hd.deriv] at h2
    exact htw ((mul_eq_zero.1 h2).resolve_left two_ne_zero)

/-- Over a compact base, an open set `T` containing the zero section contains a compact closed
neighbourhood `N` of the zero section, and there is `m > 0` such that every vector with
`s + 2t < m` lies in `N`. -/
private theorem exists_isCompact_forall_lt_mem [FiniteDimensional ℝ EB] [T2Space B]
    [CompactSpace B] [FiniteDimensional ℝ F] {Vn Vp : ∀ b, Submodule ℝ (V b)}
    (hV : ∀ b, IsCompl (Vn b) (Vp b))
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun w : TotalSpace F V ↦ (⟨w.proj, negPart hV w⟩ : TotalSpace F V))
    (Q : ∀ b, LinearMap.BilinForm ℝ (V b)) (hQn : ∀ b, ∀ v ∈ Vn b, v ≠ 0 → Q b v v < 0)
    (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v) {T : Set (TotalSpace F V)} (hTo : IsOpen T)
    (hzT : ∀ x, zeroSection F V x ∈ T)
    (hqc : ContinuousOn (fun w ↦ negSq hV Q w + 2 * posSq hV Q w) T) :
    ∃ N ⊆ T, IsCompact N ∧ IsClosed N ∧
      ∃ m, 0 < m ∧ ∀ w, negSq hV Q w + 2 * posSq hV Q w < m → w ∈ N := by
  have : LocallyCompactSpace (ModelProd HB F) := (IB.prod 𝓘(ℝ, F)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace F V) :=
    ChartedSpace.locallyCompactSpace (ModelProd HB F) _
  obtain ⟨N, hN, hZN, hNT⟩ := exists_compact_between
    (isCompact_range (Trivialization.continuous_zeroSection ℝ (F := F) (E := V))) hTo
    (range_subset_iff.2 hzT)
  have hq0 (w : TotalSpace F V) : 0 ≤ negSq hV Q w + 2 * posSq hV Q w :=
    add_nonneg (negSq_nonneg hV Q hQn w) (mul_nonneg zero_le_two (posSq_nonneg hV Q hQp w))
  -- `s + 2t` is positive off the zero section, so it has a positive minimum on `N \ interior N`.
  obtain ⟨m, hm, hmq⟩ := (hN.diff isOpen_interior).exists_forall_le'
    (hqc.mono (sdiff_subset.trans hNT)) (a := 0) fun w hw ↦ (hq0 w).lt_of_ne fun h ↦
      hw.2 (eq_zeroSection_of_negSq_add_posSq_eq_zero hV Q hQn hQp h.symm ▸
        hZN (mem_range_self _))
  refine ⟨N, hNT, hN, hN.isClosed, m, hm, fun w hw ↦ interior_subset ?_⟩
  refine mem_interior_of_lt hV (contMDiff_scale hV hVs).continuous hN.isClosed
    (fun x ↦ hZN (mem_range_self x)) hq0 (fun l w ↦ ?_) hmq hw
  rw [negSq_scale, posSq_scale]
  ring

/-- **Attaching the negative disc bundle of a quadratic normal form on a vector bundle.** Let `f`
be a smooth function on a boundaryless finite-dimensional manifold `M` and let `V` be a smooth
vector bundle over a compact Hausdorff manifold, split as `V = Vn ⊕ Vp` with smooth projection
onto `Vn`. Let `Q` be a fibrewise symmetric bilinear form, negative definite on `Vn`, positive
definite on `Vp`, for which `Vn` and `Vp` are orthogonal. Let `Θ` be a smooth partial
diffeomorphism from the total space of `V` to `M`, defined along the zero section, in which `f`
has the normal form `f (Θ w) = c + ½ Q (w, w)`. Suppose that the band `f⁻¹[c - δ, c + δ]` is
compact and that its critical points lie in the image of the zero section.

Then there is `ε₀ ∈ (0, δ]` such that for every `ε ∈ (0, ε₀]` the negative disc bundle
`D_ε = {w ∈ Vn | -½ Q (w, w) ≤ ε}` lies in the source of `Θ`, and `{f ≤ c - ε} ∪ Θ(D_ε)` is a
strong deformation retract of `{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it,
and a homotopy in `{f ≤ c + ε}` from this retraction to the identity which fixes it pointwise. -/
theorem exists_sublevel_union_image_negativeDiscBundle_deformation [FiniteDimensional ℝ E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ EB] [T2Space B]
    [CompactSpace B] [FiniteDimensional ℝ F] {f : M → ℝ} {c δ : ℝ} (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {Vn Vp : ∀ b, Submodule ℝ (V b)} (hV : ∀ b, IsCompl (Vn b) (Vp b))
    (hVs : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞ fun w : TotalSpace F V ↦
      (⟨w.proj, (Vn w.proj).projection (Vp w.proj) (hV w.proj) w.2⟩ : TotalSpace F V))
    (Q : ∀ b, LinearMap.BilinForm ℝ (V b)) (hQ : ∀ b, (Q b).IsSymm)
    (hQn : ∀ b, ∀ v ∈ Vn b, v ≠ 0 → Q b v v < 0) (hQp : ∀ b, ∀ v ∈ Vp b, v ≠ 0 → 0 < Q b v v)
    (hQnp : ∀ b, ∀ u ∈ Vn b, ∀ v ∈ Vp b, Q b u v = 0)
    (Θ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞)
    (hΘ₀ : ∀ b, zeroSection F V b ∈ Θ.source)
    (hΘf : ∀ w ∈ Θ.source, f (Θ w) = c + 2⁻¹ * Q w.proj w.2 w.2) (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ Θ '' range (zeroSection F V)) :
    ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ δ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε} ⊆ Θ.source ∧
      ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
          Θ '' {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε}))),
        (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
        Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
          (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
            Θ '' {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε}}) := by
  /- Apply `exists_sublevel_union_negativeDiscBundle_deformation` to the image of the tube, with
  `s = -½ Q (u, u)` and `t = ½ Q (v, v)` read through `Θ⁻¹`, scaling the second component. -/
  set T := tube hV Θ
  have hTo : IsOpen T := isOpen_tube hV Θ hVs
  have hTU : T ⊆ Θ.source := tube_subset_source hV Θ
  have hΘl {w : TotalSpace F V} (hw : w ∈ T) : Θ.symm (Θ w) = w := left_inv_of_mem_tube hV Θ hw
  obtain ⟨hnegs, hposs⟩ := contMDiffOn_negSq_posSq_tube hV Q Θ hfs hVs hQ hQnp hΘf
  have hqc : ContinuousOn (fun w ↦ negSq hV Q w + 2 * posSq hV Q w) T :=
    hnegs.continuousOn.add (continuousOn_const.mul hposs.continuousOn)
  obtain ⟨N, hNT, hN, hNc, m, hm, hmN⟩ := exists_isCompact_forall_lt_mem hV hVs Q hQn hQp hTo
    (zeroSection_mem_tube hV Θ hΘ₀) hqc
  obtain ⟨φ, hφ, hφ₁, hφ₀⟩ := exists_tubeScaling hV Θ hVs
  have hWo : IsOpen (Θ '' T) := Θ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hTo hTU
  have hsym := Θ.symm.contMDiffOn.mono (image_tube_subset_target hV Θ)
  have hsW : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ negSq hV Q (Θ.symm x)) (Θ '' T) :=
    hnegs.comp hsym (mapsTo_symm_image_tube hV Θ)
  have htW : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ posSq hV Q (Θ.symm x)) (Θ '' T) :=
    hposs.comp hsym (mapsTo_symm_image_tube hV Θ)
  refine ⟨min δ (m / 4), lt_min hδ (by positivity), min_le_left _ _, fun ε hε hεle ↦ ?_⟩
  have hεm : 2 * ε < m := by linarith [hεle.trans (min_le_right δ (m / 4))]
  have hεδ : ε ≤ δ := hεle.trans (min_le_left _ _)
  -- The negative disc bundle lies in `N`, hence in the tube.
  have hDT : {w : TotalSpace F V | w.2 ∈ Vn w.proj ∧ -(2⁻¹ * Q w.proj w.2 w.2) ≤ ε} ⊆ T :=
    fun w hw ↦ hNT (hmN w (by
      rw [posSq_eq_zero_of_mem hV Q hw.1, negSq_eq_of_mem hV Q hQ hQnp hw.1]
      linarith [hw.2]))
  refine ⟨hDT.trans hTU, ?_⟩
  have hband : f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' Icc (c - δ) (c + δ) :=
    preimage_mono (Icc_subset_Icc (by linarith) (by linarith))
  have key := exists_sublevel_union_negativeDiscBundle_deformation hfs hWo hsW htW
    (fun x _ ↦ negSq_nonneg hV Q hQn _) (fun x _ ↦ posSq_nonneg hV Q hQp _)
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [hΘl hw, apply_eq_sub_negSq_add_posSq hV Q Θ hQ hQnp hΘf (hTU hw)])
    (by
      rintro _ ⟨w, hw, rfl⟩ htw
      have hxW : Θ w ∈ Θ '' T := mem_image_of_mem Θ hw
      exact exists_mfderiv_eq_zero_and_ne_zero hV hVs Q Θ hTo hTU
        (fun w hw ↦ by rw [hΘl hw]) (fun w hw ↦ by rw [hΘl hw]) hw
        ((hsW.contMDiffAt (hWo.mem_nhds hxW)).mdifferentiableAt (by simp))
        ((htW.contMDiffAt (hWo.mem_nhds hxW)).mdifferentiableAt (by simp))
        (by rwa [hΘl hw] at htw))
    φ (fun _ _ ↦ by rw [hφ, negSq_scale, one_pow, one_mul]) (fun _ _ ↦ by rw [hφ, posSq_scale])
    hφ₁
    (fun τ x hx ↦ hφ₀ τ x (posPart_eq_zero_of_posSq_eq_zero hV Q hQp hx)) hε
    (isCompact_setOf_mem_image_tube hV Q Θ hN hNc hNT hqc fun w hw ↦ hmN w (by linarith))
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) hband)
    (fun x hx ↦ image_mono (range_subset_iff.2 (zeroSection_mem_tube hV Θ hΘ₀))
      (hcrit ⟨hx.1, hband hx.2⟩))
  rwa [setOf_mem_image_tube_eq_image hV Q Θ hQ hQp hQnp hDT] at key

end Attachment

end TauCeti

/-! ### Morse–Bott submanifolds -/

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Attaching the negative disc bundle of a compact Morse–Bott submanifold.** Let `i : S → M` be
a nondegenerate critical submanifold of a smooth function `f`, for a smooth embedding of a
nonempty compact manifold into a Hausdorff, second-countable, finite-dimensional, boundaryless
manifold, on which `f` takes the value `c`. Suppose that the band `f⁻¹[c - δ, c + δ]` is compact
and that its critical points lie on `i`, and let `g` be a smooth fibre metric on the normal bundle
`ν` of `i`, which defines its negative normal spaces `ν⁻`.

Then there is a smooth partial diffeomorphism `Θ` from the total space of `ν` to `M`, defined
along the zero section and sending it to `i`, with `f (Θ x) = c + ½ Hess (x, x)` for the normal
Hessian `Hess`, and some `ε₀ ∈ (0, δ]` with the following property. For every `ε ∈ (0, ε₀]` the
negative disc bundle `D_ε = {x ∈ ν⁻ | -½ Hess (x, x) ≤ ε}` lies in the source of `Θ`, and
`{f ≤ c - ε} ∪ Θ(D_ε)` is a strong deformation retract of `{f ≤ c + ε}`: there is a retraction of
`{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}` from this retraction to the identity which
fixes it pointwise. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation
    (h : i.IsNondegenerateCriticalSubmanifold f) [SecondCountableTopology M] [Nonempty S]
    [CompactSpace S] [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J ∞ S]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c δ : ℝ} (hc : ∀ s, f (i s) = c) (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ range i)
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ δ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
        {w : TotalSpace P (fun s ↦ i.NormalSpace s hn) |
          w.2 ∈ h.negativeNormalSpace hn g.toRiemannianMetric w.proj ∧
            -(2⁻¹ * h.normalHessian hn w.proj w.2 w.2) ≤ ε} ⊆ Θ.source ∧
        ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
            Θ '' {w : TotalSpace P (fun s ↦ i.NormalSpace s hn) |
              w.2 ∈ h.negativeNormalSpace hn g.toRiemannianMetric w.proj ∧
                -(2⁻¹ * h.normalHessian hn w.proj w.2 w.2) ≤ ε}))),
          (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
              Θ '' {w : TotalSpace P (fun s ↦ i.NormalSpace s hn) |
                w.2 ∈ h.negativeNormalSpace hn g.toRiemannianMetric w.proj ∧
                  -(2⁻¹ * h.normalHessian hn w.proj w.2 w.2) ≤ ε}}) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have h1 : (∞ : ℕ∞ω) + 1 = ∞ := by rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have h2 : (∞ : ℕ∞ω) + 2 = ∞ := by rw [← WithTop.coe_ofNat, ← WithTop.coe_add, top_add]
  have : IsManifold I (∞ + 1) M := by rw [h1]; infer_instance
  have : IsManifold I (∞ + 2) M := by rw [h2]; infer_instance
  have : IsManifold J (∞ + 1) S := by rw [h1]; infer_instance
  have hk : (∞ : ℕ∞ω) + 1 ≤ ∞ := h1.le
  have := i.normalSpaceContMDiffVectorBundle (m := ∞) hn hk hdim
  have : T2Space S := i.isEmbedding.t2Space
  have hf2 (s : S) : ContMDiffAt I 𝓘(ℝ) (∞ + 2) f (i s) := (hfs (i s)).of_le h2.le
  obtain ⟨Θ, hΘ₀, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
    (P := P) (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _)
    (hfs.contMDiffOn.of_le h2.le)
  refine ⟨Θ, hΘ₀, hΘi, fun x hx ↦ by rw [hΘf x hx, hc], ?_⟩
  refine exists_sublevel_union_image_negativeDiscBundle_deformation hfs
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g.toRiemannianMetric
      g.toRiemannianMetric)
    (contMDiff_projection_negativeNormalSpace hn h hk hf2 hdim g) (h.normalHessian hn)
    (h.isSymm_normalHessian hn)
    (fun s v hv hv0 ↦ h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _ hv hv0)
    (fun s v hv hv0 ↦ h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn _ hv hv0)
    (fun s u hu v hv ↦ h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn _ hu hv)
    Θ hΘ₀ (fun x hx ↦ by rw [hΘf x hx, hc]) hδ hcompact ?_
  rintro x hx
  obtain ⟨s, rfl⟩ := hcrit hx
  exact ⟨_, mem_range_self s, hΘi s⟩

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

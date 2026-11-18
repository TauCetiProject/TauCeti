/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Projection
import TauCeti.Logic.Equiv.PartialEquiv
import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# Crossing the critical level of a Morse–Bott critical submanifold

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f`, with critical
value `c`, whose points are the only critical points of a compact band `f⁻¹[c - δ, c + δ]`. Bott's
attachment theorem says that crossing the level `c` attaches the negative disc bundle of `S`. This
file proves it in the form of a strong deformation retraction: for a smooth fibre metric `g` on the
normal bundle `ν` of `S` there are a Morse–Bott chart `Θ : ν → M` of `f` and an `ε₀ > 0` such that
for `0 < ε ≤ ε₀` the sublevel `{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε}` together
with the image under `Θ` of the negative disc bundle `{x ∈ ν⁻ | -½ Hess (x, x) ≤ ε}`, where `ν⁻` is
the negative normal bundle of `g` and `Hess` the normal Hessian. This is the deformation step of
Bott's theorem, from which the relative homology of the crossing is read off through the Thom pair
of `ν⁻`.

The proof joins two results already available. The Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`, in the
namespace `TauCeti.SmoothEmbedding`) gives `Θ` with `f ∘ Θ = c + ½ Hess` near the zero section.
The attachment theorem for a tube written on `M`
(`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`) needs functions `s, t ≥ 0` with
`f = c - s + t` and a scaling of the positive directions. The metric `g` splits each normal space
as `ν⁻ ⊕ ν⁺`, orthogonally both for `g` and for `Hess`, with smooth projections
(`IsNondegenerateCriticalSubmanifold.contMDiff_projection_negativeNormalSpace` and its positive
counterpart). Writing a normal vector as `x = u + v` accordingly, `½ Hess (x, x) = -s + t` for
`s = -½ Hess (u, u)` and `t = ½ Hess (v, v)`, and the scaling is `(τ, u + v) ↦ u + τ v`. On the
tube `{‖x‖_g < ρ}`, which lies in the source of `Θ` for some `ρ > 0` because `S` is compact, `s`
and `t` are smooth since `s = c - f ∘ Θ` of the projection onto `ν⁻`, and the tube is preserved by
the scaling and both projections. Finally `s + t` is bounded below by a positive multiple of
`‖x‖²_g`, by compactness of a sphere bundle and homogeneity, so for small `ε` the disc bundle and
the part `{s + 2t ≤ 2ε}` of the tube lie in a compact half tube. The compactness of `S` itself
follows from that of the band.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`:
  crossing the level of a Morse–Bott critical submanifold attaches its negative disc bundle, up to
  a strong deformation retraction.

In the namespace `TauCeti`:

* `exists_sublevel_union_image_deformation`: the attachment theorem
  `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation` with its tube data given in the
  source of a partial diffeomorphism into `M`.
* `exists_sublevel_union_image_negativeDiscBundle_deformation`: crossing the level of a quadratic
  normal form `f ∘ Θ = c + ½ Q` on a Riemannian vector bundle over a compact base attaches the
  image under `Θ` of the negative disc bundle of `Q`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

open Bundle Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Transport

variable {E H M EN HN N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {f : M → ℝ} {c ε : ℝ} {Θ : PartialDiffeomorph IN I N M ∞} {T : Set N} {s t : N → ℝ}
  {φ : ℝ × N → N}

/-- Along a curve `γ`, a function that is eventually constant has derivative `0` in the direction
of `γ`, and one that is eventually `τ² a` has derivative `2a`. -/
private theorem exists_mfderiv_eq_zero_ne_zero {s t : M → ℝ} {γ : ℝ → M} {p : M} (hγp : γ 1 = p)
    {a : ℝ} (ha : a ≠ 0) (hγ : MDifferentiableAt 𝓘(ℝ) I γ 1)
    (hs : MDifferentiableAt I 𝓘(ℝ) s p) (ht : MDifferentiableAt I 𝓘(ℝ) t p) {b : ℝ}
    (hsγ : s ∘ γ =ᶠ[𝓝 1] fun _ ↦ b) (htγ : t ∘ γ =ᶠ[𝓝 1] fun τ ↦ τ ^ 2 * a) :
    ∃ v : TangentSpace I p, mfderiv I 𝓘(ℝ) s p v = 0 ∧ mfderiv I 𝓘(ℝ) t p v ≠ 0 := by
  subst hγp
  -- `mvfderiv` of a real function is its `mfderiv`, read in `ℝ`.
  have hcomp {u : M → ℝ} (hu : MDifferentiableAt I 𝓘(ℝ) u (γ 1)) :
      HasDerivAt (u ∘ γ) (mfderiv I 𝓘(ℝ) u (γ 1) (Manifold.curveVelocity I γ 1)) 1 :=
    Manifold.hasDerivAt_comp_curve hu (Manifold.hasMFDerivAt_curveVelocity hγ)
  refine ⟨Manifold.curveVelocity I γ 1, (hcomp hs).unique ?_, ?_⟩
  · exact (hasDerivAt_const 1 b).congr_of_eventuallyEq hsγ
  · rw [(hcomp ht).unique (((hasDerivAt_pow 2 (1 : ℝ)).mul_const a).congr_of_eventuallyEq htγ)]
    -- The goal lives in a tangent space of `ℝ`; state it in `ℝ`.
    exact (by simpa using ha : ((2 : ℕ) : ℝ) * 1 ^ (2 - 1) * a ≠ 0)

/-- At a point `Θ x` of the tube with `t x ≠ 0`, the velocity at `τ = 1` of the curve
`τ ↦ Θ (φ (τ, x))` is killed by `d(s ∘ Θ⁻¹)` but not by `d(t ∘ Θ⁻¹)`. -/
private theorem exists_mfderiv_comp_symm_eq_zero_ne_zero (hT : IsOpen T) (hTΘ : T ⊆ Θ.source)
    (hsW : ContMDiffOn I 𝓘(ℝ) ∞ (s ∘ Θ.symm) (Θ '' T))
    (htW : ContMDiffOn I 𝓘(ℝ) ∞ (t ∘ Θ.symm) (Θ '' T)) (hφc : Continuous φ)
    (hφs : ∀ τ x, s (φ (τ, x)) = s x) (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x)
    (hφ₁ : ∀ x, φ (1, x) = x) {x : N} (hx : x ∈ T)
    (hφd : MDifferentiableAt 𝓘(ℝ) IN (fun τ ↦ φ (τ, x)) 1) (htx : t x ≠ 0) :
    ∃ v : TangentSpace I (Θ x), mfderiv I 𝓘(ℝ) (s ∘ Θ.symm) (Θ x) v = 0 ∧
      mfderiv I 𝓘(ℝ) (t ∘ Θ.symm) (Θ x) v ≠ 0 := by
  have hinv (x : N) (hx : x ∈ T) : Θ.symm (Θ x) = x := Θ.left_inv (hTΘ hx)
  have hW : IsOpen (Θ '' T) := Θ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hT hTΘ
  -- The curve `τ ↦ Θ (φ (τ, x))` stays in the tube near `τ = 1`.
  have hev : ∀ᶠ τ in 𝓝 (1 : ℝ), φ (τ, x) ∈ T :=
    (hφc.comp (continuous_id.prodMk continuous_const)).continuousAt.preimage_mem_nhds
      (by simpa [hφ₁] using hT.mem_nhds hx)
  have hdiff {u : M → ℝ} (hu : ContMDiffOn I 𝓘(ℝ) ∞ u (Θ '' T)) :
      MDifferentiableAt I 𝓘(ℝ) u (Θ x) :=
    (hu.mdifferentiableOn (by simp) _ ⟨x, hx, rfl⟩).mdifferentiableAt (hW.mem_nhds ⟨x, hx, rfl⟩)
  refine exists_mfderiv_eq_zero_ne_zero (γ := fun τ ↦ Θ (φ (τ, x))) (by simp [hφ₁]) htx
    ((Θ.mdifferentiableAt (by simp) (by simpa [hφ₁] using hTΘ hx)).comp (1 : ℝ) hφd)
    (hdiff hsW) (hdiff htW) (b := s x) ?_ ?_
  · filter_upwards [hev] with τ hτ
    simp only [comp_apply, hinv _ hτ, hφs]
  · filter_upwards [hev] with τ hτ
    simp only [comp_apply, hinv _ hτ, hφt]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Attaching the negative disc bundle through a partial diffeomorphism.** This is
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation` with its tube data `s, t, φ` given
on an open set `T` in the source of a partial diffeomorphism `Θ` into `M`, rather than on `M`: the
tube is `Θ '' T` and the attached disc bundle is the image of `{x ∈ T | t x = 0, s x ≤ ε}`. The
tangent vectors killed by `ds` but not by `dt` are not required: they are the velocities of the
curves `τ ↦ Θ (φ (τ, x))` at `τ = 1`. -/
theorem exists_sublevel_union_image_deformation (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hT : IsOpen T) (hTΘ : T ⊆ Θ.source) (hs : ContMDiffOn IN 𝓘(ℝ) ∞ s T)
    (ht : ContMDiffOn IN 𝓘(ℝ) ∞ t T) (hs₀ : ∀ x ∈ T, 0 ≤ s x) (ht₀ : ∀ x ∈ T, 0 ≤ t x)
    (hf : ∀ x ∈ T, f (Θ x) = c - s x + t x) (hφc : Continuous φ)
    (hφd : ∀ x ∈ T, MDifferentiableAt 𝓘(ℝ) IN (fun τ ↦ φ (τ, x)) 1)
    (hφT : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x ∈ T, φ (τ, x) ∈ T) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ x, t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ T ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ Θ '' T) :
    ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩
        ({x | f x ≤ c - ε} ∪ Θ '' {x | x ∈ T ∧ t x = 0 ∧ s x ≤ ε}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _)
        {x | (x : M) ∈ {x | f x ≤ c - ε} ∪ Θ '' {x | x ∈ T ∧ t x = 0 ∧ s x ≤ ε}}) := by
  have hmem := Set.ext_iff.1 (Θ.toPartialEquiv.image_eq_target_inter_inv_preimage hTΘ)
  have hinv (x : N) (hx : x ∈ T) : Θ.symm (Θ x) = x := Θ.left_inv (hTΘ hx)
  have hΘsymm : ContMDiffOn I IN ∞ Θ.symm (Θ '' T) :=
    Θ.symm.contMDiffOn.mono fun y hy ↦ ((hmem y).1 hy).1
  have hsW : ContMDiffOn I 𝓘(ℝ) ∞ (s ∘ Θ.symm) (Θ '' T) :=
    hs.comp hΘsymm fun y hy ↦ ((hmem y).1 hy).2
  have htW : ContMDiffOn I 𝓘(ℝ) ∞ (t ∘ Θ.symm) (Θ '' T) :=
    ht.comp hΘsymm fun y hy ↦ ((hmem y).1 hy).2
  -- The scaling of the positive directions, read on `M`.
  have hφT' (p : unitInterval × ↥(Θ '' T)) : φ (p.1, Θ.symm p.2) ∈ T :=
    hφT p.1 p.1.2 _ ((hmem _).1 p.2.2).2
  let φW : C(unitInterval × ↥(Θ '' T), ↥(Θ '' T)) :=
    { toFun := fun p ↦ ⟨Θ (φ (p.1, Θ.symm p.2)), ⟨_, hφT' p, rfl⟩⟩
      continuous_toFun := (Θ.contMDiffOn.continuousOn.comp_continuous (hφc.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (hΘsymm.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_snd)
            fun p ↦ p.2.2))) fun p ↦ hTΘ (hφT' p)).subtype_mk _ }
  have hφW (p : unitInterval × ↥(Θ '' T)) : Θ.symm (φW p) = φ (p.1, Θ.symm p.2) :=
    hinv _ (hφT' p)
  have hD : {y | y ∈ Θ '' T ∧ (t ∘ Θ.symm) y = 0 ∧ (s ∘ Θ.symm) y ≤ ε} =
      Θ '' {x | x ∈ T ∧ t x = 0 ∧ s x ≤ ε} :=
    (Θ.toPartialEquiv.image_inter_of_subset_source hTΘ {x | t x = 0 ∧ s x ≤ ε}).symm
  rw [← hD]
  refine exists_sublevel_union_negativeDiscBundle_deformation hfs
    (Θ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hT hTΘ) hsW htW
    (fun y hy ↦ hs₀ _ ((hmem y).1 hy).2) (fun y hy ↦ ht₀ _ ((hmem y).1 hy).2) (fun y hy ↦ ?_)
    (fun y hy hty ↦ ?_) φW (fun τ y ↦ ?_) (fun τ y ↦ ?_) (fun y ↦ ?_) (fun τ y hy ↦ ?_) hε ?_
    hcompact hcrit
  · obtain ⟨x, hx, rfl⟩ := hy
    simp only [comp_apply, hinv x hx]
    exact hf x hx
  · obtain ⟨x, hx, rfl⟩ := hy
    simp only [comp_apply, hinv x hx] at hty
    exact exists_mfderiv_comp_symm_eq_zero_ne_zero hT hTΘ hsW htW hφc hφs hφt hφ₁ hx
      (hφd x hx) hty
  · simp only [comp_apply, hφW, hφs]
  · simp only [comp_apply, hφW, hφt]
  · ext
    simp only [ContinuousMap.coe_mk, φW, Set.Icc.coe_one, hφ₁]
    exact Θ.right_inv ((hmem y).1 y.2).1
  · ext
    simp only [ContinuousMap.coe_mk, φW]
    rw [hφ₀ _ _ hy]
    exact Θ.right_inv ((hmem y).1 y.2).1
  · have hKW : {y | y ∈ Θ '' T ∧ (s ∘ Θ.symm) y + 2 * (t ∘ Θ.symm) y ≤ 2 * ε} =
        Θ '' {x | x ∈ T ∧ s x + 2 * t x ≤ 2 * ε} :=
      (Θ.toPartialEquiv.image_inter_of_subset_source hTΘ {x | s x + 2 * t x ≤ 2 * ε}).symm
    rw [hKW]
    exact hK.image_of_continuousOn (Θ.contMDiffOn.continuousOn.mono fun x hx ↦ hTΘ hx.1)

end Transport

section QuadraticTube

/-! ### The tube of a quadratic normal form on a Riemannian vector bundle -/

variable {B F : Type*} {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)]
  {Q : ∀ b, LinearMap.BilinForm ℝ (V b)} {Nn Pp : ∀ b, Submodule ℝ (V b)}
  (hNP : ∀ b, IsCompl (Nn b) (Pp b))

/-- The component in `Nn b` of a vector of the fibre over `b`, along `Pp b`. -/
private noncomputable def negPart (b : B) (w : V b) : V b :=
  (Nn b).projection (Pp b) (hNP b) w

/-- The component in `Pp b` of a vector of the fibre over `b`, along `Nn b`. -/
private noncomputable def posPart (b : B) (w : V b) : V b :=
  (Pp b).projection (Nn b) (hNP b).symm w

variable (Q) in
/-- Minus half the quadratic form on the `Nn`-component: the squared norm `‖u‖²` of the negative
directions in the normal form `c - ‖u‖² + ‖v‖²`. -/
private noncomputable def tubeNeg (x : TotalSpace F V) : ℝ :=
  -(2⁻¹ * Q x.proj (negPart hNP x.proj x.2) (negPart hNP x.proj x.2))

variable (Q) in
/-- Half the quadratic form on the `Pp`-component: the squared norm `‖v‖²` of the positive
directions in the normal form `c - ‖u‖² + ‖v‖²`. -/
private noncomputable def tubePos (x : TotalSpace F V) : ℝ :=
  2⁻¹ * Q x.proj (posPart hNP x.proj x.2) (posPart hNP x.proj x.2)

/-- The scaling `(τ, u + v) ↦ u + τ v` of the positive directions. -/
private noncomputable def tubeScale (p : ℝ × TotalSpace F V) : TotalSpace F V :=
  ⟨p.2.proj, negPart hNP p.2.proj p.2.2 + p.1 • posPart hNP p.2.proj p.2.2⟩

private theorem negPart_mem (b : B) (w : V b) : negPart hNP b w ∈ Nn b :=
  Submodule.projection_apply_mem _ _

private theorem posPart_mem (b : B) (w : V b) : posPart hNP b w ∈ Pp b :=
  Submodule.projection_apply_mem _ _

private theorem negPart_add_posPart (b : B) (w : V b) : negPart hNP b w + posPart hNP b w = w :=
  Submodule.projection_add_projection_eq_self _ _

private theorem negPart_add {b : B} {n p : V b} (hn : n ∈ Nn b) (hp : p ∈ Pp b) :
    negPart hNP b (n + p) = n :=
  Submodule.projection_add_of_mem (hNP b) hn hp

private theorem posPart_add {b : B} {n p : V b} (hn : n ∈ Nn b) (hp : p ∈ Pp b) :
    posPart hNP b (n + p) = p :=
  Submodule.projection_add_of_mem' (hNP b) hn hp

private theorem tubeScale_one (x : TotalSpace F V) : tubeScale hNP (1, x) = x := by
  obtain ⟨b, w⟩ := x
  simp only [tubeScale, one_smul, negPart_add_posPart]

private theorem tubeNeg_tubeScale (τ : ℝ) (x : TotalSpace F V) :
    tubeNeg Q hNP (tubeScale hNP (τ, x)) = tubeNeg Q hNP x := by
  obtain ⟨b, w⟩ := x
  dsimp only [tubeNeg, tubeScale]
  rw [negPart_add hNP (negPart_mem hNP b w) (Submodule.smul_mem _ τ (posPart_mem hNP b w))]

private theorem tubePos_tubeScale (τ : ℝ) (x : TotalSpace F V) :
    tubePos Q hNP (tubeScale hNP (τ, x)) = τ ^ 2 * tubePos Q hNP x := by
  obtain ⟨b, w⟩ := x
  dsimp only [tubePos, tubeScale]
  rw [posPart_add hNP (negPart_mem hNP b w) (Submodule.smul_mem _ τ (posPart_mem hNP b w))]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The scaling only shortens vectors for `τ ∈ [0, 1]`. -/
private theorem norm_tubeScale_le (hgNP : ∀ b, ∀ v ∈ Nn b, ∀ w ∈ Pp b, inner ℝ v w = 0)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (x : TotalSpace F V) :
    ‖(tubeScale hNP (τ, x)).2‖ ≤ ‖x.2‖ := by
  obtain ⟨b, w⟩ := x
  have h₁ : ‖w‖ ^ 2 = ‖negPart hNP b w‖ ^ 2 + ‖posPart hNP b w‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_projection_of_isCompl (hNP b) (hgNP b) w
  have h₂ := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (negPart hNP b w)
    (τ • posPart hNP b w) (by
      rw [inner_smul_right, hgNP b _ (negPart_mem hNP b w) _ (posPart_mem hNP b w), mul_zero])
  simp only [← sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h₂
  -- `dsimp` would keep the fibre norm indexed by the unreduced base point of the scaled vector.
  change ‖negPart hNP b w + τ • posPart hNP b w‖ ≤ ‖w‖
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h₁, h₂]
  nlinarith [pow_le_one₀ hτ.1 hτ.2 (n := 2), sq_nonneg ‖posPart hNP b w‖]

/-- On the negative directions, `‖u‖²` is minus half the quadratic form. -/
private theorem tubeNeg_of_mem {x : TotalSpace F V} (hx : x.2 ∈ Nn x.proj) :
    tubeNeg Q hNP x = -(2⁻¹ * Q x.proj x.2 x.2) := by
  rw [tubeNeg, negPart, Submodule.projection_apply_of_mem_left _ hx]

/-- Half the quadratic form is `-‖u‖² + ‖v‖²`. -/
private theorem half_apply_self_eq (hQ : ∀ b, (Q b).IsSymm)
    (hQNP : ∀ b, ∀ v ∈ Nn b, ∀ w ∈ Pp b, Q b v w = 0) (x : TotalSpace F V) :
    2⁻¹ * Q x.proj x.2 x.2 = -tubeNeg Q hNP x + tubePos Q hNP x := by
  rw [(hQ x.proj).isRefl.apply_self_eq_add_projection (hNP x.proj) (hQNP x.proj) x.2]
  simp only [tubeNeg, tubePos, negPart, posPart]
  ring

variable (hQN : ∀ b, ∀ v ∈ Nn b, v ≠ 0 → Q b v v < 0) (hQP : ∀ b, ∀ v ∈ Pp b, v ≠ 0 → 0 < Q b v v)
include hQN hQP

omit hQP in
private theorem tubeNeg_nonneg (x : TotalSpace F V) : 0 ≤ tubeNeg Q hNP x := by
  rcases eq_or_ne (negPart hNP x.proj x.2) 0 with h | h
  · simp [tubeNeg, h]
  · have := hQN _ _ (negPart_mem hNP _ _) h
    simp only [tubeNeg]
    linarith

omit hQN in
private theorem tubePos_nonneg (x : TotalSpace F V) : 0 ≤ tubePos Q hNP x := by
  rcases eq_or_ne (posPart hNP x.proj x.2) 0 with h | h
  · simp [tubePos, h]
  · have := hQP _ _ (posPart_mem hNP _ _) h
    simp only [tubePos]
    linarith

omit hQN in
private theorem posPart_eq_zero_of_tubePos_eq_zero {x : TotalSpace F V}
    (hx : tubePos Q hNP x = 0) : posPart hNP x.proj x.2 = 0 := by
  by_contra h
  have := hQP _ _ (posPart_mem hNP _ _) h
  simp only [tubePos] at hx
  linarith

/-- `‖u‖² + ‖v‖²` vanishes only on the zero section. -/
private theorem tubeNeg_add_tubePos_pos {x : TotalSpace F V} (hx : x.2 ≠ 0) :
    0 < tubeNeg Q hNP x + tubePos Q hNP x := by
  rw [← negPart_add_posPart hNP x.proj x.2] at hx
  rcases eq_or_ne (negPart hNP x.proj x.2) 0 with hn | hn
  · rw [hn, zero_add] at hx
    have := hQP _ _ (posPart_mem hNP _ _) hx
    have := tubeNeg_nonneg hNP hQN x
    simp only [tubePos]
    linarith
  · have := hQN _ _ (negPart_mem hNP _ _) hn
    have := tubePos_nonneg hNP hQP x
    simp only [tubeNeg]
    linarith

omit hQN hQP in
/-- `‖u‖² + ‖v‖²` is homogeneous of degree two in the fibre. -/
private theorem tubeNeg_add_tubePos_smul (b : B) (a : ℝ) (w : V b) :
    tubeNeg Q hNP (⟨b, a • w⟩ : TotalSpace F V) + tubePos Q hNP (⟨b, a • w⟩ : TotalSpace F V) =
      a ^ 2 * (tubeNeg Q hNP (⟨b, w⟩ : TotalSpace F V) +
        tubePos Q hNP (⟨b, w⟩ : TotalSpace F V)) := by
  simp only [tubeNeg, tubePos, negPart, posPart, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hQN in
/-- `‖v‖²` vanishes exactly on the negative directions. -/
private theorem tubePos_eq_zero_iff {x : TotalSpace F V} :
    tubePos Q hNP x = 0 ↔ x.2 ∈ Nn x.proj := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [← negPart_add_posPart hNP x.proj x.2, posPart_eq_zero_of_tubePos_eq_zero hNP hQP hx,
      add_zero]
    exact negPart_mem hNP _ _
  · rw [tubePos, posPart, (Submodule.projection_apply_eq_zero_iff _).2 hx]
    simp

omit hQN in
/-- Inside the tube of radius `ρ`, the points with `‖v‖² = 0` and `‖u‖² ≤ ε` form the negative disc
bundle `{x ∈ Nn | -½ Q (x, x) ≤ ε}`, provided that the latter lies in the half tube. -/
private theorem setOf_tubePos_eq_zero_eq {ρ ε : ℝ} (hρ : 0 < ρ)
    (hsmall : ∀ x : TotalSpace F V, tubeNeg Q hNP x + tubePos Q hNP x ≤ ε → ‖x.2‖ ≤ ρ / 2) :
    {x : TotalSpace F V | x ∈ {x : TotalSpace F V | ‖x.2‖ < ρ} ∧ tubePos Q hNP x = 0 ∧
      tubeNeg Q hNP x ≤ ε} = {x | x.2 ∈ Nn x.proj ∧ -(2⁻¹ * Q x.proj x.2 x.2) ≤ ε} := by
  ext x
  constructor
  · rintro ⟨-, h0, hle⟩
    have hmem := (tubePos_eq_zero_iff hNP hQP).1 h0
    exact ⟨hmem, tubeNeg_of_mem hNP hmem ▸ hle⟩
  · rintro ⟨hmem, hle⟩
    have h0 := (tubePos_eq_zero_iff hNP hQP).2 hmem
    rw [← tubeNeg_of_mem hNP hmem] at hle
    have := hsmall x (by rw [h0, add_zero]; exact hle)
    exact ⟨this.trans_lt (half_lt_self hρ), h0, hle⟩

omit hQN in
/-- The scaling fixes the negative directions. -/
private theorem tubeScale_of_tubePos_eq_zero (τ : ℝ) {x : TotalSpace F V}
    (hx : tubePos Q hNP x = 0) : tubeScale hNP (τ, x) = x := by
  obtain ⟨b, w⟩ := x
  have h := posPart_eq_zero_of_tubePos_eq_zero hNP hQP hx
  rw [tubeScale]
  simp only at h ⊢
  rw [h, smul_zero, add_zero, ← add_zero (negPart hNP b w), ← h, negPart_add_posPart]

end QuadraticTube

section QuadraticTubeBundle

/-! ### Radius and smoothness of the tube -/

variable {B F : Type*} [TopologicalSpace B] [CompactSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  {Q : ∀ b, LinearMap.BilinForm ℝ (V b)} {Nn Pp : ∀ b, Submodule ℝ (V b)}
  (hNP : ∀ b, IsCompl (Nn b) (Pp b))

/-- If the sublevel `{‖u‖² + 2‖v‖² ≤ 2ε}` of the tube of radius `ρ` lies in the half tube, it is
compact. -/
private theorem isCompact_setOf_mem_tube {ρ ε : ℝ} (hρ : 0 < ρ)
    (hs : ContinuousOn (tubeNeg Q hNP) {x : TotalSpace F V | ‖x.2‖ < ρ})
    (ht : ContinuousOn (tubePos Q hNP) {x : TotalSpace F V | ‖x.2‖ < ρ})
    (hsmall : ∀ x : TotalSpace F V, tubeNeg Q hNP x + 2 * tubePos Q hNP x ≤ 2 * ε →
      ‖x.2‖ ≤ ρ / 2) :
    IsCompact {x | x ∈ {x : TotalSpace F V | ‖x.2‖ < ρ} ∧
      tubeNeg Q hNP x + 2 * tubePos Q hNP x ≤ 2 * ε} := by
  have hC : IsCompact {x : TotalSpace F V | ‖x.2‖ ≤ ρ / 2} :=
    isCompact_setOf_norm_le_bundle continuous_const
  have hCT : {x : TotalSpace F V | ‖x.2‖ ≤ ρ / 2} ⊆ {x | ‖x.2‖ < ρ} :=
    fun x (hx : ‖x.2‖ ≤ ρ / 2) ↦ hx.trans_lt (half_lt_self hρ)
  have hq : ContinuousOn (fun x ↦ tubeNeg Q hNP x + 2 * tubePos Q hNP x)
      {x : TotalSpace F V | ‖x.2‖ < ρ} :=
    hs.add (continuousOn_const.mul ht)
  have hcl := (hq.mono hCT).preimage_isClosed_of_isClosed
    (isClosed_le (continuous_norm_bundle F V) continuous_const) (isClosed_Iic (a := 2 * ε))
  convert hC.of_isClosed_subset hcl inter_subset_left using 1
  ext x
  exact ⟨fun hx ↦ ⟨hsmall x hx.2, hx.2⟩, fun hx ↦ ⟨hCT hx.1, hx.2⟩⟩

variable (hQN : ∀ b, ∀ v ∈ Nn b, v ≠ 0 → Q b v v < 0) (hQP : ∀ b, ∀ v ∈ Pp b, v ≠ 0 → 0 < Q b v v)
include hQN hQP

/-- If `‖u‖² + ‖v‖²` is continuous on a fibre sphere bundle, it is bounded below by a positive
multiple of the squared fibre norm. -/
private theorem exists_mul_norm_sq_le {ρ : ℝ} (hρ : 0 < ρ)
    (hq : ContinuousOn (fun x ↦ tubeNeg Q hNP x + tubePos Q hNP x)
      {x : TotalSpace F V | ‖x.2‖ = ρ}) :
    ∃ m > 0, ∀ x : TotalSpace F V, m * ‖x.2‖ ^ 2 ≤ tubeNeg Q hNP x + tubePos Q hNP x := by
  obtain ⟨m₀, hm₀, hm₀S⟩ := (isCompact_setOf_norm_eq_bundle continuous_const).exists_forall_le'
    hq (a := (0 : ℝ)) fun x hx ↦ tubeNeg_add_tubePos_pos hNP hQN hQP fun h ↦ by
      simp only [mem_ofPred_eq, h, norm_zero] at hx
      linarith
  refine ⟨m₀ / ρ ^ 2, by positivity, fun x ↦ ?_⟩
  obtain ⟨b, w⟩ := x
  rcases eq_or_ne w 0 with rfl | hw
  · simpa using add_nonneg (tubeNeg_nonneg hNP hQN _) (tubePos_nonneg hNP hQP _)
  -- Rescale `w` onto the sphere of radius `ρ`.
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hmem : ‖(ρ / ‖w‖) • w‖ = ρ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hwpos.ne']
  have h := hm₀S ⟨b, (ρ / ‖w‖) • w⟩ hmem
  rw [tubeNeg_add_tubePos_smul, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

end QuadraticTubeBundle

section Smooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  {Q : ∀ b, LinearMap.BilinForm ℝ (V b)} {Nn Pp : ∀ b, Submodule ℝ (V b)}
  (hNP : ∀ b, IsCompl (Nn b) (Pp b)) {f : M → ℝ} {c : ℝ}
  {Θ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞} {T : Set (TotalSpace F V)}

/-- On a part `T` of the source of a normal form `f ∘ Θ = c + ½ Q`, preserved by the projection
onto the negative directions, `‖u‖²` is smooth: it is `c - f ∘ Θ` of that projection. -/
private theorem contMDiffOn_tubeNeg (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * Q x.proj x.2 x.2)
    (hneg : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦ (⟨x.proj, negPart hNP x.proj x.2⟩ : TotalSpace F V))
    (hTΘ : T ⊆ Θ.source)
    (hT : MapsTo (fun x : TotalSpace F V ↦ (⟨x.proj, negPart hNP x.proj x.2⟩ : TotalSpace F V))
      T T) :
    ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ (tubeNeg Q hNP) T := by
  refine ((contMDiffOn_const (c := c)).sub (hfs.comp_contMDiffOn
    (Θ.contMDiffOn.comp hneg.contMDiffOn fun x hx ↦ hTΘ (hT hx)))).congr fun x hx ↦ ?_
  simp only [comp_apply, hΘf _ (hTΘ (hT hx)), tubeNeg]
  ring

/-- On a part `T` of the source of a normal form `f ∘ Θ = c + ½ Q`, preserved by the projection
onto the positive directions, `‖v‖²` is smooth: it is `f ∘ Θ - c` of that projection. -/
private theorem contMDiffOn_tubePos (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * Q x.proj x.2 x.2)
    (hpos : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦ (⟨x.proj, posPart hNP x.proj x.2⟩ : TotalSpace F V))
    (hTΘ : T ⊆ Θ.source)
    (hT : MapsTo (fun x : TotalSpace F V ↦ (⟨x.proj, posPart hNP x.proj x.2⟩ : TotalSpace F V))
      T T) :
    ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞ (tubePos Q hNP) T := by
  refine ((hfs.comp_contMDiffOn (Θ.contMDiffOn.comp hpos.contMDiffOn
    fun x hx ↦ hTΘ (hT hx))).sub (contMDiffOn_const (c := c))).congr fun x hx ↦ ?_
  simp only [comp_apply, hΘf _ (hTΘ (hT hx)), tubePos]
  ring

variable [VectorBundle ℝ F V] in
/-- The scaling of the positive directions is smooth when the two projections are. -/
private theorem contMDiff_tubeScale
    (hneg : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦ (⟨x.proj, negPart hNP x.proj x.2⟩ : TotalSpace F V))
    (hpos : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦ (⟨x.proj, posPart hNP x.proj x.2⟩ : TotalSpace F V)) :
    ContMDiff (𝓘(ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞ (tubeScale (F := F) hNP) :=
  ContMDiff.add_sectionAlong (F := F) (V := V) (b := fun p : ℝ × TotalSpace F V ↦ p.2.proj)
    (s := fun p ↦ negPart hNP p.2.proj p.2.2) (t := fun p ↦ p.1 • posPart hNP p.2.proj p.2.2)
    (hneg.comp contMDiff_snd)
    (contMDiff_fst.smul_totalSpace (F := F) (V := V) (hpos.comp contMDiff_snd))

end Smooth

section Tube

/-! ### Crossing the level of a quadratic normal form on a Riemannian vector bundle -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : B → Type*}
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V]
  {Q : ∀ b, LinearMap.BilinForm ℝ (V b)} {Nn Pp : ∀ b, Submodule ℝ (V b)}
  (hNP : ∀ b, IsCompl (Nn b) (Pp b)) {f : M → ℝ} {c : ℝ}
  {Θ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) M ∞}

/-- **Attaching the negative disc bundle of a quadratic normal form.** Let `Θ` be a partial
diffeomorphism from a Riemannian vector bundle over a compact base to `M`, defined on the zero
section, in which `f = c + ½ Q` for fibrewise symmetric bilinear forms `Q`. Suppose that each fibre
splits into `Q`-orthogonal and metric-orthogonal subspaces `Nn ⊕ Pp`, on which `Q` is negative,
respectively positive, definite, with smooth projections. Then for all small `ε > 0` the negative
disc bundle `{x ∈ Nn | -½ Q (x, x) ≤ ε}` lies in the source of `Θ`, and if the band
`f⁻¹[c - ε, c + ε]` is compact with its critical points on the image of the zero section, then
`M_{c-ε}` with the image of this disc bundle is a strong deformation retract of `M_{c+ε}`. -/
theorem exists_sublevel_union_image_negativeDiscBundle_deformation (hQ : ∀ b, (Q b).IsSymm)
    (hQNP : ∀ b, ∀ v ∈ Nn b, ∀ w ∈ Pp b, Q b v w = 0)
    (hgNP : ∀ b, ∀ v ∈ Nn b, ∀ w ∈ Pp b, inner ℝ v w = 0)
    (hQN : ∀ b, ∀ v ∈ Nn b, v ≠ 0 → Q b v v < 0) (hQP : ∀ b, ∀ v ∈ Pp b, v ≠ 0 → 0 < Q b v v)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hzero : ∀ b, (⟨b, 0⟩ : TotalSpace F V) ∈ Θ.source)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * Q x.proj x.2 x.2)
    (hneg : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦
        (⟨x.proj, (Nn x.proj).projection (Pp x.proj) (hNP x.proj) x.2⟩ : TotalSpace F V))
    (hpos : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      fun x : TotalSpace F V ↦
        (⟨x.proj, (Pp x.proj).projection (Nn x.proj) (hNP x.proj).symm x.2⟩ : TotalSpace F V)) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      {x : TotalSpace F V | x.2 ∈ Nn x.proj ∧ -(2⁻¹ * Q x.proj x.2 x.2) ≤ ε} ⊆ Θ.source ∧
      (IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆
          range (fun b ↦ Θ (⟨b, 0⟩ : TotalSpace F V)) →
        ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
            Θ '' {x : TotalSpace F V | x.2 ∈ Nn x.proj ∧ -(2⁻¹ * Q x.proj x.2 x.2) ≤ ε}))),
          (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
              Θ '' {x : TotalSpace F V | x.2 ∈ Nn x.proj ∧ -(2⁻¹ * Q x.proj x.2 x.2) ≤ ε}})) := by
  -- The tube `T` of radius `ρ` lies in the source of `Θ`; on it `‖u‖²` and `‖v‖²` are smooth.
  obtain ⟨ρ, hρ, hρs⟩ :=
    isCompact_univ.exists_pos_forall_norm_le_subset_bundle Θ.open_source fun b _ ↦ hzero b
  set T := {x : TotalSpace F V | ‖x.2‖ < ρ}
  have hT : IsOpen T := isOpen_lt (continuous_norm_bundle F V) continuous_const
  have hTΘ : T ⊆ Θ.source := fun x (hx : ‖x.2‖ < ρ) ↦ hρs x.proj (mem_univ _) x.2 hx.le
  have hsT := contMDiffOn_tubeNeg hNP (Q := Q) hfs hΘf hneg hTΘ
    fun x hx ↦ (Submodule.norm_projection_le_of_isCompl (hNP _) (hgNP _) x.2).trans_lt hx
  have htT := contMDiffOn_tubePos hNP (Q := Q) hfs hΘf hpos hTΘ
    fun x hx ↦ (Submodule.norm_projection_le_of_isCompl (hNP _).symm
      (fun v hv w hw ↦ inner_eq_zero_symm.1 (hgNP _ w hw v hv)) x.2).trans_lt hx
  -- `‖u‖² + ‖v‖²` controls the fibre norm, so its small sublevels lie in the half tube.
  obtain ⟨m, hm, hmq⟩ := exists_mul_norm_sq_le hNP hQN hQP (half_pos hρ)
    ((hsT.continuousOn.add htT.continuousOn).mono fun x (hx : ‖x.2‖ = ρ / 2) ↦
      hx.trans_lt (half_lt_self hρ))
  refine ⟨m * ρ ^ 2 / 8, by positivity, fun ε hε ↦ ?_⟩
  have hsmall (x : TotalSpace F V) (hx : tubeNeg Q hNP x + tubePos Q hNP x ≤ 2 * ε) :
      ‖x.2‖ ≤ ρ / 2 := by
    have h := hmq x
    have h2 : ‖x.2‖ ^ 2 ≤ (ρ / 2) ^ 2 := by nlinarith [hε.2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hD := setOf_tubePos_eq_zero_eq (Q := Q) hNP hQP hρ (ε := ε)
    fun x hx ↦ hsmall x (by linarith [hε.1])
  refine ⟨hD ▸ fun x hx ↦ hTΘ hx.1, fun hcompact hcrit ↦ ?_⟩
  rw [← hD]
  exact exists_sublevel_union_image_deformation hfs hT hTΘ hsT htT
    (fun x _ ↦ tubeNeg_nonneg hNP hQN x) (fun x _ ↦ tubePos_nonneg hNP hQP x)
    (fun x hx ↦ by rw [hΘf x (hTΘ hx), half_apply_self_eq hNP hQ hQNP x]; ring)
    (contMDiff_tubeScale hNP hneg hpos).continuous
    (fun x _ ↦ ((contMDiff_tubeScale hNP hneg hpos).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp))
    (fun τ hτ x hx ↦ (norm_tubeScale_le hNP hgNP hτ x).trans_lt hx)
    (tubeNeg_tubeScale hNP) (tubePos_tubeScale hNP) (tubeScale_one hNP)
    (fun τ x hx ↦ tubeScale_of_tubePos_eq_zero hNP hQP τ hx) hε.1
    (isCompact_setOf_mem_tube hNP hρ hsT.continuousOn htT.continuousOn fun x hx ↦ hsmall x (by
      have := tubePos_nonneg hNP hQP x
      linarith)) hcompact
    (hcrit.trans (range_subset_iff.2 fun b ↦ ⟨⟨b, 0⟩, by simpa [T] using hρ, rfl⟩))

end Tube

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' S P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- A critical submanifold at the level `c` whose points are all the critical points of a compact
band around `c` is compact. -/
private theorem compactSpace_of_isCompact (h : i.IsCriticalSubmanifold f)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c δ : ℝ} (hδ : 0 < δ) (hc : ∀ s, f (i s) = c)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ range i) : CompactSpace S := by
  have hband {y : M} (hy : f y = c) : y ∈ f ⁻¹' Icc (c - δ) (c + δ) := by
    rw [mem_preimage, hy]
    exact ⟨by linarith, by linarith⟩
  have hrange : range i = criticalPoints I f ∩ f ⁻¹' {c} := by
    ext y
    refine ⟨?_, fun hy ↦ hcrit ⟨hy.1, hband hy.2⟩⟩
    rintro ⟨s, rfl⟩
    exact ⟨h.mem_criticalPoints s, hc s⟩
  refine isCompact_univ_iff.1 (i.isEmbedding.isCompact_iff.2 ?_)
  rw [image_univ, hrange]
  exact hcompact.of_isClosed_subset ((isClosed_criticalPoints (hf.of_le (by simp))).inter
    (isClosed_singleton.preimage hf.continuous)) fun y hy ↦ hband hy.2

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SecondCountableTopology M]
  [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J ∞ S] [Nonempty S]

/-- **Attaching the negative disc bundle across the level of a Morse–Bott critical submanifold**
(Bott; Milnor's Theorem 3.2 run fibrewise). Let `i : S → M` be a nondegenerate critical submanifold
of a smooth function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless
manifold, with critical value `c`, and let `g` be a smooth fibre metric on its normal bundle `ν`,
with negative normal spaces `ν⁻ = h.negativeNormalSpace hn g`. Suppose that the band
`f⁻¹[c - δ, c + δ]` is compact and that its critical points all lie on `S`; in particular `S` is
compact.

Then there is a Morse–Bott normal-bundle chart `Θ` from `ν` to `M`, sending the zero section to `i`
and putting `f` in the form `f (Θ x) = c + ½ Hess (x, x)` with `Hess` the normal Hessian, and some
`0 < ε₀ ≤ δ` such that for every `0 < ε ≤ ε₀` the negative disc bundle
`D = {x ∈ ν⁻ | -½ Hess (x, x) ≤ ε}` lies in the source of `Θ`, and the sublevel `{f ≤ c + ε}`
strong deformation retracts onto `{f ≤ c - ε}` together with `Θ '' D`: there is a retraction of
`{f ≤ c + ε}` onto this set and a homotopy, fixing it pointwise, from the retraction to the
identity. The submanifold `S` need not be connected, and the index may vary along it. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation
    (h : i.IsNondegenerateCriticalSubmanifold f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ} (hc : ∀ s, f (i s) = c)
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
    {δ : ℝ} (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ) ⊆ range i) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ ∈ Ioc 0 δ, ∀ ε ∈ Ioc 0 ε₀,
        let D := {x : TotalSpace P (fun s ↦ i.NormalSpace s hn) |
          x.2 ∈ h.negativeNormalSpace hn g.toRiemannianMetric x.proj ∧
            -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ≤ ε}
        D ⊆ Θ.source ∧
        ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪ Θ '' D))),
          (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪ Θ '' D}) := by
  have : CompactSpace S :=
    compactSpace_of_isCompact h.toIsCriticalSubmanifold hf hδ hc hcompact hcrit
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have htop : (∞ : ℕ∞ω) + 2 ≤ ∞ := by
    rw [← WithTop.coe_ofNat, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 le_top
  have : IsManifold I (∞ + 2) M := .of_le htop
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by
    rw [← WithTop.coe_one, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 le_top)
  -- The fibre metric `g` makes `ν` a continuous Riemannian bundle. These are the instances of
  -- `Bundle.RiemannianBundle`, which typeclass inference cannot find for `i.NormalSpace s hn`.
  let (s : S) : NormedAddCommGroup (i.NormalSpace s hn) :=
    (g.toRiemannianMetric.toCore s).toNormedAddCommGroupOfTopology
      (g.toRiemannianMetric.continuousAt s) (g.toRiemannianMetric.isVonNBounded s)
  let (s : S) : InnerProductSpace ℝ (i.NormalSpace s hn) :=
    .ofCoreOfTopology (g.toRiemannianMetric.toCore s) (g.toRiemannianMetric.continuousAt s)
      (g.toRiemannianMetric.isVonNBounded s)
  have : IsContinuousRiemannianBundle P fun s ↦ i.NormalSpace s hn :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  -- The Morse–Bott lemma on the normal bundle.
  obtain ⟨Θ, hzero, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
    (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _) (hf.of_le htop).contMDiffOn
  have hΘf' (x) (hx : x ∈ Θ.source) : f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2 := by
    rw [hΘf x hx, hc]
  have hfi (s : S) : ContMDiffAt I 𝓘(ℝ) (∞ + 2) f (i s) := (hf.of_le htop).contMDiffAt
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_sublevel_union_image_negativeDiscBundle_deformation
    (Q := fun s ↦ h.normalHessian hn s)
    (fun s ↦ h.isCompl_negativeNormalSpace_positiveNormalSpace hn g.toRiemannianMetric
      g.toRiemannianMetric s)
    (fun s ↦ h.isSymm_normalHessian hn s)
    (fun _ _ hv _ hw ↦ h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn _ hv hw)
    (fun _ _ hv _ hw ↦ h.inner_eq_zero_of_mem_negativeNormalSpace hn _ hv hw)
    (fun _ _ hv hv0 ↦ h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _ hv hv0)
    (fun _ _ hv hv0 ↦ h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn _ hv hv0)
    hf hzero hΘf'
    (h.contMDiff_projection_negativeNormalSpace hn (k := ∞) (by simp) hfi hdim g)
    (h.contMDiff_projection_positiveNormalSpace hn (k := ∞) (by simp) hfi hdim g)
  refine ⟨Θ, hΘi, hΘf', min ε₀ δ, ⟨lt_min hε₀ hδ, min_le_right _ _⟩, fun ε hε ↦ ?_⟩
  obtain ⟨hDs, hret⟩ := hmain ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεδ : ε ≤ δ := hε.2.trans (min_le_right _ _)
  have hband : f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' Icc (c - δ) (c + δ) :=
    preimage_mono (Icc_subset_Icc (by linarith) (by linarith))
  refine ⟨hDs, hret (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous) hband)
    fun y hy ↦ ?_⟩
  obtain ⟨s, rfl⟩ := hcrit ⟨hy.1, hband hy.2⟩
  exact ⟨s, hΘi s⟩

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold



end TauCeti

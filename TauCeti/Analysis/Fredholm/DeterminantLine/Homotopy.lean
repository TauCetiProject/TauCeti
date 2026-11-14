/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.OrientationCover
public import TauCeti.Topology.VectorBundle.Orientation.Cover.FundamentalGroup
import Mathlib.Topology.Homotopy.Lifting

/-!
# Homotopy invariance and covering monodromy of Fredholm determinant orientations

Along a continuous path of Fredholm operators `T : ℝ → E →L[ℝ] F`,
`TauCeti.detLineOrientationTransport` carries orientations of `(T a).detLine` to orientations of
`(T b).detLine` by following coherent families of determinant-line elements
(`TauCeti.Analysis.Fredholm.DeterminantLine.Transport`). Because `ContinuousOn` subsumes `C¹` paths
via `ContDiffOn.continuousOn`, all transport laws proved for continuous Fredholm families apply
directly to `C¹` (and higher-regularity) paths as well.

This file develops endpoint-relative homotopy invariance and the covering-monodromy transport
package for Fredholm determinant orientations in both unbundled (`ℝ → E →L[ℝ] F`) and bundled
(`{T : E →L[ℝ] F // T.IsFredholm}`) form:

* **Rectangle commutativity and endpoint-relative homotopy invariance of
  `TauCeti.detLineOrientationTransport`.** Over a parameter rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`,
  convexity yields a coherent family over the entire rectangle
  (`TauCeti.exists_isDetLineCoherentOn_of_convex`), so the two boundary routes from `(s₀, a)` to
  `(s₁, b)` induce the same orientation transport (`TauCeti.detLineOrientationTransport_prod_comm`).
  Specializing to families constant on the vertical edges gives endpoint-relative homotopy
  invariance (`TauCeti.detLineOrientationTransport_slice_eq_of_homotopyRel`,
  `TauCeti.detLineOrientationTransport_eq_of_homotopyRel`) and path-independence inside any convex
  set of Fredholm operators (`TauCeti.detLineOrientationTransport_eq_of_convex`).
* **Bundled path and homotopy-class transport via covering monodromy.** Conjugating the general
  orientation-cover monodromy `TauCeti.VectorBundleOrientationCover.quotientTransport` of
  `TauCeti.FredholmDetLine` by `TauCeti.FredholmDetLine.orientationEquivRay` defines orientation
  transport on path homotopy classes (`TauCeti.FredholmDetLine.quotientOrientationTransport`) and
  on paths (`TauCeti.FredholmDetLine.pathOrientationTransport`), satisfying identity, reversal,
  concatenation, negation, unit-scaling, and endpoint-relative homotopy invariance, and agreeing
  with `TauCeti.detLineOrientationTransport`
  (`TauCeti.FredholmDetLine.pathOrientationTransport_mk_eq_detLineOrientationTransport`,
  `TauCeti.FredholmDetLine.pathOrientationTransport_apply_eq_map_detLineOrientationTransport`).
  Specializing `TauCeti.VectorBundleOrientationCover.orientationCharacter` to `FredholmDetLine`
  yields the loop orientation monodromy character
  `TauCeti.FredholmDetLine.orientationMonodromySign : FundamentalGroup _ T₀ →* ℤˣ`.

## Main definitions

* `TauCeti.FredholmDetLine.quotientOrientationTransport`: orientation transport along a homotopy
  class of paths in `{T : E →L[ℝ] F // T.IsFredholm}` via covering monodromy.
* `TauCeti.FredholmDetLine.pathOrientationTransport`: orientation transport along a continuous
  `Path` of Fredholm operators.
* `TauCeti.FredholmDetLine.orientationMonodromySign`: homomorphism `FundamentalGroup _ T₀ →* ℤˣ`
  recording whether monodromy around a loop preserves (`1`) or reverses (`-1`) determinant-line
  orientation.

## Main results

* `TauCeti.detLineOrientationTransport_prod_comm`: commutativity of orientation transport around the
  boundary of a parameter rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`.
* `TauCeti.detLineOrientationTransport_slice_eq_of_homotopyRel`,
  `TauCeti.detLineOrientationTransport_eq_of_homotopyRel`: endpoint-relative homotopy invariance of
  `TauCeti.detLineOrientationTransport`.
* `TauCeti.detLineOrientationTransport_eq_of_convex`: path-independence of orientation transport for
  paths with common endpoints in a convex set of Fredholm operators.
* `TauCeti.IsDetLineCoherentOn.monodromy_orientationCoverMk`,
  `TauCeti.FredholmDetLine.pathOrientationTransport_mk_eq_detLineOrientationTransport`,
  `TauCeti.FredholmDetLine.pathOrientationTransport_apply_eq_map_detLineOrientationTransport`:
  agreement between covering-monodromy transport and `TauCeti.detLineOrientationTransport`.
* `TauCeti.FredholmDetLine.quotientOrientationTransport_toPath_eq_smul`,
  `TauCeti.FredholmDetLine.orientationMonodromySign_eq_one_iff`,
  `TauCeti.FredholmDetLine.orientationMonodromySign_eq_neg_one_iff`: action and sign
  characterizations of `orientationMonodromySign`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Bundle Filter Set Topology Module ContinuousLinearMap

namespace TauCeti

section UnbundledHomotopy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem continuousOn_slice_left {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b s : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b)) (hs : s ∈ uIcc s₀ s₁) :
    ContinuousOn (fun t ↦ H (s, t)) (uIcc a b) :=
  hH.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨hs, ht⟩

private theorem continuousOn_slice_right {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b t : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b)) (ht : t ∈ uIcc a b) :
    ContinuousOn (fun s ↦ H (s, t)) (uIcc s₀ s₁) :=
  hH.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, ht⟩

private theorem isDetLineCoherentOn_slice_left {H : ℝ × ℝ → E →L[ℝ] F}
    {v : ∀ p, (H p : E →ₗ[ℝ] F).detLine} {s₀ s₁ a b s : ℝ}
    (hv : IsDetLineCoherentOn H v (uIcc s₀ s₁ ×ˢ uIcc a b)) (hs : s ∈ uIcc s₀ s₁) :
    IsDetLineCoherentOn (fun t ↦ H (s, t)) (fun t ↦ v (s, t)) (uIcc a b) :=
  hv.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨hs, ht⟩

private theorem isDetLineCoherentOn_slice_right {H : ℝ × ℝ → E →L[ℝ] F}
    {v : ∀ p, (H p : E →ₗ[ℝ] F).detLine} {s₀ s₁ a b t : ℝ}
    (hv : IsDetLineCoherentOn H v (uIcc s₀ s₁ ×ˢ uIcc a b)) (ht : t ∈ uIcc a b) :
    IsDetLineCoherentOn (fun s ↦ H (s, t)) (fun s ↦ v (s, t)) (uIcc s₀ s₁) :=
  hv.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, ht⟩

variable [CompleteSpace E] [CompleteSpace F]

/-- **Commutativity of orientation transport around a parameter rectangle.** For a family
`H : ℝ × ℝ → E →L[ℝ] F` that is continuous and Fredholm on `[[s₀, s₁]] ×ˢ [[a, b]]`, transporting an
orientation from `(s₀, a)` to `(s₀, b)` and then to `(s₁, b)` agrees with transporting from
`(s₀, a)` to `(s₁, a)` and then to `(s₁, b)`. -/
theorem detLineOrientationTransport_prod_comm {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm)
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm)
    (hHa : ContinuousOn (fun s ↦ H (s, a)) (uIcc s₀ s₁))
    (hFa : ∀ s ∈ uIcc s₀ s₁, (H (s, a)).IsFredholm)
    (hHb : ContinuousOn (fun s ↦ H (s, b)) (uIcc s₀ s₁))
    (hFb : ∀ s ∈ uIcc s₀ s₁, (H (s, b)).IsFredholm)
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁ hHb hFb
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) =
      detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁ hHa hFa o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  -- Extend `v₀` at `(s₀, a)` to a coherent family on the convex rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`.
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_of_convex
    ((convex_uIcc s₀ s₁).prod (convex_uIcc a b)) hH hF ⟨left_mem_uIcc, left_mem_uIcc⟩ hv₀
  rw [detLineOrientationTransport_rayOfNeZero hHs₀ hFs₀
      (isDetLineCoherentOn_slice_left hv left_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero hHb hFb
      (isDetLineCoherentOn_slice_right hv right_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero hHa hFa
      (isDetLineCoherentOn_slice_right hv left_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero hHs₁ hFs₁
      (isDetLineCoherentOn_slice_left hv right_mem_uIcc)]

/-- **Endpoint-relative homotopy invariance of orientation transport for slices.** If
`H : ℝ × ℝ → E →L[ℝ] F` is continuous and Fredholm on `[[s₀, s₁]] ×ˢ [[a, b]]` and keeps both
endpoints `H (·, a)` and `H (·, b)` constant on `[[s₀, s₁]]`, then the slices `H (s₀, ·)` and
`H (s₁, ·)` induce the same orientation transport from `a` to `b`. -/
theorem detLineOrientationTransport_slice_eq_of_homotopyRel {H : ℝ × ℝ → E →L[ℝ] F}
    {s₀ s₁ a b : ℝ} (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = H (s₀, a))
    (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = H (s₀, b))
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm)
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm)
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (ha s₁ right_mem_uIcc).symm)) o) =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb s₁ right_mem_uIcc).symm))
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) := by
  have hHa := continuousOn_slice_right hH (t := a) left_mem_uIcc
  have hFa : ∀ s ∈ uIcc s₀ s₁, (H (s, a)).IsFredholm := fun s hs ↦ hF (s, a) ⟨hs, left_mem_uIcc⟩
  have hHb := continuousOn_slice_right hH (t := b) right_mem_uIcc
  have hFb : ∀ s ∈ uIcc s₀ s₁, (H (s, b)).IsFredholm := fun s hs ↦ hF (s, b) ⟨hs, right_mem_uIcc⟩
  rw [← detLineOrientationTransport_of_forall_eq_const hHa hFa ha o,
    ← detLineOrientationTransport_prod_comm hH hF hHs₀ hFs₀ hHs₁ hFs₁ hHa hFa hHb hFb o,
    detLineOrientationTransport_of_forall_eq_const hHb hFb hb]

/-- **Endpoint-relative homotopy invariance between two paths.** If `T₀, T₁ : ℝ → E →L[ℝ] F` are
joined on `[[s₀, s₁]] ×ˢ [[a, b]]` by a continuous Fredholm homotopy `H` with `H (s₀, ·) = T₀`,
`H (s₁, ·) = T₁`, and constant vertical edges `H (·, a) = T₀ a`, `H (·, b) = T₀ b`, then `T₀` and
`T₁` induce the same orientation transport. -/
theorem detLineOrientationTransport_eq_of_homotopyRel
    {T₀ T₁ : ℝ → E →L[ℝ] F} {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hF₀ : ∀ t ∈ uIcc a b, (T₀ t).IsFredholm)
    (hT₁ : ContinuousOn T₁ (uIcc a b)) (hF₁ : ∀ t ∈ uIcc a b, (T₁ t).IsFredholm)
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hFH : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (hs₀ : ∀ t ∈ uIcc a b, H (s₀, t) = T₀ t)
    (hs₁ : ∀ t ∈ uIcc a b, H (s₁, t) = T₁ t)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = T₀ a)
    (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = T₀ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((ha s₁ right_mem_uIcc).symm.trans (hs₁ a left_mem_uIcc)))) o) =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((hb s₁ right_mem_uIcc).symm.trans (hs₁ b right_mem_uIcc))))
        (detLineOrientationTransport a b hT₀ hF₀ o) := by
  have hHs₀ := continuousOn_slice_left hH (s := s₀) left_mem_uIcc
  have hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm := fun t ht ↦ hFH (s₀, t) ⟨left_mem_uIcc, ht⟩
  have hHs₁ := continuousOn_slice_left hH (s := s₁) right_mem_uIcc
  have hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm := fun t ht ↦ hFH (s₁, t) ⟨right_mem_uIcc, ht⟩
  have ha' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, a) = H (s₀, a) :=
    (ha s hs).trans (ha s₀ left_mem_uIcc).symm
  have hb' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, b) = H (s₀, b) :=
    (hb s hs).trans (hb s₀ left_mem_uIcc).symm
  let e₀a := congrArg ContinuousLinearMap.toLinearMap (hs₀ a left_mem_uIcc).symm
  let ea := congrArg ContinuousLinearMap.toLinearMap (ha' s₁ right_mem_uIcc).symm
  let e₁a := congrArg ContinuousLinearMap.toLinearMap (hs₁ a left_mem_uIcc)
  let o' := Module.Ray.map (LinearMap.detLineOfEq e₀a) o
  let o₁ := Module.Ray.map (LinearMap.detLineOfEq ea) o'
  have hin₁ : Module.Ray.map (LinearMap.detLineOfEq e₁a) o₁ =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap
        ((ha s₁ right_mem_uIcc).symm.trans (hs₁ a left_mem_uIcc)))) o := by
    simp only [o₁, o', Module.Ray.map_detLineOfEq_map_detLineOfEq]
  have hin₀ : Module.Ray.map (LinearMap.detLineOfEq
      (congrArg ContinuousLinearMap.toLinearMap (hs₀ a left_mem_uIcc))) o' = o := by
    simp only [o', Module.Ray.map_detLineOfEq_map_detLineOfEq,
      LinearMap.detLineOfEq_rfl, Module.Ray.map_refl, Equiv.refl_apply]
  have hc₀ := detLineOrientationTransport_congr hHs₀ hT₀ hFs₀ hF₀ hs₀ o'
  rw [hin₀] at hc₀
  have hc₁ := detLineOrientationTransport_congr hHs₁ hT₁ hFs₁ hF₁ hs₁ o₁
  have hhom := detLineOrientationTransport_slice_eq_of_homotopyRel
    hH hFH ha' hb' hHs₀ hFs₀ hHs₁ hFs₁ o'
  rw [← hin₁, hc₁, hhom, hc₀, Module.Ray.map_detLineOfEq_map_detLineOfEq,
    Module.Ray.map_detLineOfEq_map_detLineOfEq]

/-- **Path-independence in a convex set of Fredholm operators.** Any two continuous paths
`T₀, T₁ : ℝ → E →L[ℝ] F` taking values in a convex set `U` of Fredholm operators (for example, an
affine coset of compact perturbations of a fixed Fredholm operator) and sharing endpoints at `a` and
`b` induce the same orientation transport. -/
theorem detLineOrientationTransport_eq_of_convex {U : Set (E →L[ℝ] F)} (hU : Convex ℝ U)
    (hUF : ∀ S ∈ U, S.IsFredholm) {T₀ T₁ : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hT₀U : ∀ t ∈ uIcc a b, T₀ t ∈ U) (hT₁U : ∀ t ∈ uIcc a b, T₁ t ∈ U)
    (ha : T₀ a = T₁ a) (hb : T₀ b = T₁ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
        (Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap ha)) o) =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap hb))
        (detLineOrientationTransport a b hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) o) := by
  let H : ℝ × ℝ → E →L[ℝ] F := fun p ↦ (1 - p.1) • T₀ p.2 + p.1 • T₁ p.2
  have hmaps : MapsTo Prod.snd (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) (uIcc a b) := fun _ hp ↦ hp.2
  have hH : ContinuousOn H (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    ((continuousOn_const.sub continuous_fst.continuousOn).smul
      (hT₀.comp continuous_snd.continuousOn hmaps)).add
      (continuous_fst.continuousOn.smul (hT₁.comp continuous_snd.continuousOn hmaps))
  have hHU (p : ℝ × ℝ) (hp : p ∈ uIcc (0 : ℝ) 1 ×ˢ uIcc a b) : H p ∈ U := by
    have hs : p.1 ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (zero_le_one' ℝ)] using hp.1
    exact hU (hT₀U p.2 hp.2) (hT₁U p.2 hp.2) (sub_nonneg.2 hs.2) hs.1 (sub_add_cancel 1 p.1)
  exact detLineOrientationTransport_eq_of_homotopyRel
    hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
    hH (fun p hp ↦ hUF _ (hHU p hp))
    (fun t _ ↦ by simp [H]) (fun t _ ↦ by simp [H])
    (fun s _ ↦ by simp [H, ← ha, sub_smul])
    (fun s _ ↦ by simp [H, ← hb, sub_smul]) o

end UnbundledHomotopy

/-- Along a continuous Fredholm family `T : ℝ → E →L[ℝ] F` on `[[0, 1]]`, covering monodromy of the
orientation double cover carries the initial ray of a coherent family `v` to its final ray. -/
theorem IsDetLineCoherentOn.monodromy_orientationCoverMk
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℝ → E →L[ℝ] F} {v : ∀ t, (T t : E →ₗ[ℝ] F).detLine}
    (hv : IsDetLineCoherentOn T v (uIcc 0 1))
    (hT : ContinuousOn T (uIcc 0 1)) (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm) :
    (FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy
      (.mk ⟨⟨fun t : unitInterval ↦ ⟨T t.1, hF t.1 (Icc_subset_uIcc t.2)⟩,
        (hT.comp_continuous continuous_subtype_val
          fun t ↦ Icc_subset_uIcc t.2).subtype_mk _⟩, rfl, rfl⟩)
      ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1) ⟨T 0, hF 0 left_mem_uIcc⟩).symm
        (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))) =
    ⟨FredholmDetLine.orientationCoverMk (Fin 1) ⟨T 1, hF 1 right_mem_uIcc⟩
      (rayOfNeZero ℝ (v 1) (hv.ne_zero right_mem_uIcc)),
      FredholmDetLine.proj_orientationCoverMk _ _⟩ := by
  -- Coherent `v` induces a continuous lift `g_sub` on `[[0, 1]]`; restricting to `unitInterval`
  -- exhibits the unique path lift determining `IsCoveringMap.monodromy`.
  obtain ⟨hv_ne, hg⟩ :=
    (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hT hF).1 hv
  let g_sub : uIcc (0 : ℝ) 1 → VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) :=
    fun x ↦ FredholmDetLine.orientationCoverMk (Fin 1) ⟨T x.1, hF x.1 x.2⟩
      (rayOfNeZero ℝ (v x.1) (hv_ne x.1 x.2))
  let ιI : unitInterval → uIcc (0 : ℝ) 1 := fun t ↦ ⟨t.1, Icc_subset_uIcc t.2⟩
  let Γ : C(unitInterval, VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ⟨g_sub ∘ ιI, hg.comp (continuous_subtype_val.subtype_mk _)⟩
  let γ : Path (⟨T 0, hF 0 left_mem_uIcc⟩ : {T : E →L[ℝ] F // T.IsFredholm})
      ⟨T 1, hF 1 right_mem_uIcc⟩ :=
    ⟨⟨fun t : unitInterval ↦ ⟨T t.1, hF t.1 (Icc_subset_uIcc t.2)⟩,
      (hT.comp_continuous continuous_subtype_val
        fun t ↦ Icc_subset_uIcc t.2).subtype_mk _⟩, rfl, rfl⟩
  have hpΓ : (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) → _) ∘ ⇑Γ = ⇑γ :=
    funext fun _ ↦ FredholmDetLine.proj_orientationCoverMk _ _
  have hΓ0 : Γ 0 = ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1)
      ⟨T 0, hF 0 left_mem_uIcc⟩).symm (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))).1 := by
    rw [FredholmDetLine.orientationCoverFiberEquiv_symm_apply]
    exact congrArg g_sub (Subtype.ext rfl)
  have hΓ1 : Γ 1 = FredholmDetLine.orientationCoverMk (Fin 1) ⟨T 1, hF 1 right_mem_uIcc⟩
      (rayOfNeZero ℝ (v 1) (hv.ne_zero right_mem_uIcc)) :=
    congrArg g_sub (Subtype.ext rfl)
  refine Subtype.ext ?_
  rw [(FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F)
    (ι := Fin 1)).monodromy_eq_apply_one hpΓ hΓ0, hΓ1]

namespace FredholmDetLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Orientation transport along a path homotopy class.** Obtained by conjugating
`VectorBundleOrientationCover.quotientTransport` of `FredholmDetLine ℝ E F` by
`FredholmDetLine.orientationEquivRay`. -/
def quotientOrientationTransport {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) :
    Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.1 : E →ₗ[ℝ] F).detLine :=
  ((orientationEquivRay (ι := Fin 1) T₀).symm.trans
    (VectorBundleOrientationCover.quotientTransport (F := ℝ) (E := FredholmDetLine ℝ E F)
      (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ)).trans
    (orientationEquivRay (ι := Fin 1) T₁)

theorem quotientOrientationTransport_def {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ =
      ((orientationEquivRay (ι := Fin 1) T₀).symm.trans
        (VectorBundleOrientationCover.quotientTransport (F := ℝ) (E := FredholmDetLine ℝ E F)
          (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ)).trans
        (orientationEquivRay (ι := Fin 1) T₁) :=
  (rfl)

-- Keep this lemma for explicit rewriting: a simp attribute unfolds the left-hand side of
-- `quotientOrientationTransport_neg` and `quotientOrientationTransport_units_smul`, failing
-- the `simpNF` linter.
theorem quotientOrientationTransport_apply {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ r =
      orientationCoverFiberEquiv (Fin 1) T₁
        ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy γ
          ((orientationCoverFiberEquiv (Fin 1) T₀).symm r)) := by
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_apply,
    orientationCoverFiberEquiv_def]

@[simp]
theorem quotientOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    quotientOrientationTransport (.refl T₀) = Equiv.refl _ := by
  ext r
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_symm {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ.symm = (quotientOrientationTransport γ).symm := by
  ext r
  simp [quotientOrientationTransport_def]

/-- Concatenation law for orientation transport along path homotopy classes. -/
theorem quotientOrientationTransport_trans {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ₁ : Path.Homotopic.Quotient T₀ T₁) (γ₂ : Path.Homotopic.Quotient T₁ T₂) :
    quotientOrientationTransport (γ₁.trans γ₂) =
      (quotientOrientationTransport γ₁).trans (quotientOrientationTransport γ₂) := by
  ext r
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_trans]

@[simp]
theorem quotientOrientationTransport_neg {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (-r) = -quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_units_smul {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) (u : ℝˣ)
    (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (u • r) = u • quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

/-- **Orientation transport along a continuous path of Fredholm operators.** Defined by descending
`γ : Path T₀ T₁` to its homotopy class in `Path.Homotopic.Quotient T₀ T₁`. -/
def pathOrientationTransport {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.1 : E →ₗ[ℝ] F).detLine :=
  quotientOrientationTransport (.mk γ)

theorem pathOrientationTransport_def {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    pathOrientationTransport γ = quotientOrientationTransport (.mk γ) :=
  (rfl)

@[simp]
theorem pathOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    pathOrientationTransport (Path.refl T₀) = Equiv.refl _ := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_refl,
    quotientOrientationTransport_refl]

@[simp]
theorem pathOrientationTransport_symm {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    pathOrientationTransport γ.symm = (pathOrientationTransport γ).symm := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_symm,
    quotientOrientationTransport_symm, pathOrientationTransport_def]

/-- Concatenation law for orientation transport along continuous paths of Fredholm operators. -/
theorem pathOrientationTransport_trans {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ₁ : Path T₀ T₁) (γ₂ : Path T₁ T₂) :
    pathOrientationTransport (γ₁.trans γ₂) =
      (pathOrientationTransport γ₁).trans (pathOrientationTransport γ₂) := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_trans,
    quotientOrientationTransport_trans, pathOrientationTransport_def, pathOrientationTransport_def]

/-- **Endpoint-relative homotopy invariance** for `Path`s in `{T : E →L[ℝ] F // T.IsFredholm}`. -/
theorem pathOrientationTransport_eq_of_homotopic {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    {γ₀ γ₁ : Path T₀ T₁} (h : γ₀.Homotopic γ₁) :
    pathOrientationTransport γ₀ = pathOrientationTransport γ₁ := by
  rw [pathOrientationTransport_def, pathOrientationTransport_def, Path.Homotopic.Quotient.eq.2 h]

/-- Compatibility of `pathOrientationTransport` with `Path.cast` along endpoint equalities. -/
theorem pathOrientationTransport_cast {S₀ S₁ T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path S₀ S₁) (h₀ : T₀ = S₀) (h₁ : T₁ = S₁)
    (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport (γ.cast h₀ h₁) o =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) h₁.symm))
        (pathOrientationTransport γ
          (Module.Ray.map (LinearMap.detLineOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) h₀)) o)) := by
  subst h₀
  subst h₁
  simp

@[simp]
theorem pathOrientationTransport_neg {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path T₀ T₁) (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (-r) = -pathOrientationTransport γ r :=
  quotientOrientationTransport_neg (.mk γ) r

@[simp]
theorem pathOrientationTransport_units_smul {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path T₀ T₁) (u : ℝˣ) (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (u • r) = u • pathOrientationTransport γ r :=
  quotientOrientationTransport_units_smul (.mk γ) u r

/-- **Agreement of covering monodromy and coherent-family transport.** For an unbundled family
`T : ℝ → E →L[ℝ] F` that is continuous and Fredholm on `[[0, 1]]`, covering-monodromy transport
along the induced `Path` on `unitInterval` coincides with `TauCeti.detLineOrientationTransport` from
`0` to `1`. -/
theorem pathOrientationTransport_mk_eq_detLineOrientationTransport
    {T : ℝ → E →L[ℝ] F} (hT : ContinuousOn T (uIcc 0 1))
    (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm)
    (o : Module.Ray ℝ (T 0 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport
        (⟨⟨fun t : unitInterval ↦ ⟨T t.1, hF t.1 (Icc_subset_uIcc t.2)⟩,
          (hT.comp_continuous continuous_subtype_val
            fun t ↦ Icc_subset_uIcc t.2).subtype_mk _⟩, rfl, rfl⟩ :
          Path ⟨T 0, hF 0 left_mem_uIcc⟩ ⟨T 1, hF 1 right_mem_uIcc⟩) o =
      detLineOrientationTransport 0 1 hT hF o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  have hmon := hv.monodromy_orientationCoverMk hT hF
  rw [pathOrientationTransport_def, quotientOrientationTransport_apply, hmon,
    orientationCoverFiberEquiv_mk' ⟨T 1, hF 1 right_mem_uIcc⟩,
    detLineOrientationTransport_rayOfNeZero hT hF hv]

/-- **Bridge between `pathOrientationTransport` and `detLineOrientationTransport`.** For any path
`γ : Path T₀ T₁` in `{T : E →L[ℝ] F // T.IsFredholm}`, covering-monodromy orientation transport
along `γ` agrees with `TauCeti.detLineOrientationTransport` along `γ.extend` from `0` to `1`. -/
theorem pathOrientationTransport_apply_eq_map_detLineOrientationTransport
    {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path T₀ T₁) (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ o =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) γ.extend_one))
        (detLineOrientationTransport (T := fun t ↦ (γ.extend t).1) 0 1
          (continuous_subtype_val.comp γ.continuous_extend).continuousOn
          (fun t _ ↦ (γ.extend t).2)
          (Module.Ray.map (LinearMap.detLineOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F))
              γ.extend_zero.symm)) o)) := by
  have hT : ContinuousOn (fun t ↦ (γ.extend t).1) (uIcc 0 1) :=
    (continuous_subtype_val.comp γ.continuous_extend).continuousOn
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, ((γ.extend t).1).IsFredholm := fun t _ ↦ (γ.extend t).2
  let γ' : Path (γ.extend 0) (γ.extend 1) :=
    ⟨⟨fun t : unitInterval ↦ ⟨(γ.extend t.1).1, hF t.1 (Icc_subset_uIcc t.2)⟩,
      (hT.comp_continuous continuous_subtype_val
        fun t ↦ Icc_subset_uIcc t.2).subtype_mk _⟩, rfl, rfl⟩
  have hγ : pathOrientationTransport γ =
      pathOrientationTransport (γ'.cast γ.extend_zero.symm γ.extend_one.symm) :=
    congrArg pathOrientationTransport
      (Path.ext (funext fun t ↦ Subtype.ext (congrArg Subtype.val (γ.extend_extends' t).symm)))
  simp only [hγ, pathOrientationTransport_cast]
  congr 1
  exact pathOrientationTransport_mk_eq_detLineOrientationTransport hT hF _

/-- Around any loop homotopy class based at `T₀`, orientation transport either fixes every ray or
reverses every ray. -/
theorem quotientOrientationTransport_eq_self_or_eq_neg {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₀) :
    (∀ r, quotientOrientationTransport γ r = r) ∨
      (∀ r, quotientOrientationTransport γ r = -r) := by
  rcases VectorBundleOrientationCover.quotientTransport_eq_self_or_eq_neg
    (F := ℝ) (E := FredholmDetLine ℝ E F) (ι := Fin 1)
    (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ with h | h
  · exact .inl fun r ↦ by simp [quotientOrientationTransport_def, h]
  · exact .inr fun r ↦ by simp [quotientOrientationTransport_def, h]

/-- **Orientation monodromy sign character.** Homomorphism from the fundamental group of
`{T : E →L[ℝ] F // T.IsFredholm}` at `T₀` to `ℤˣ` taking value `1` on orientation-preserving loops
and `-1` on orientation-reversing loops, defined as
`VectorBundleOrientationCover.orientationCharacter` of `FredholmDetLine ℝ E F`. -/
def orientationMonodromySign (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ :=
  VectorBundleOrientationCover.orientationCharacter (F := ℝ) (E := FredholmDetLine ℝ E F)
    (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀

theorem orientationMonodromySign_def (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    orientationMonodromySign T₀ =
      VectorBundleOrientationCover.orientationCharacter (F := ℝ) (E := FredholmDetLine ℝ E F)
        (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀ :=
  (rfl)

/-- Orientation transport along a loop class `γ : FundamentalGroup _ T₀` acts on every ray in
`(T₀.1 : E →ₗ[ℝ] F).detLine` by its `orientationMonodromySign`. -/
theorem quotientOrientationTransport_toPath_eq_smul {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ.toPath r =
      (Units.map (Int.castRingHom ℝ).toMonoidHom (orientationMonodromySign T₀ γ)) • r := by
  simp [quotientOrientationTransport_def,
    VectorBundleOrientationCover.quotientTransport_toPath_eq_smul, orientationMonodromySign_def]

/-- `orientationMonodromySign` equals `1` if and only if orientation transport along `γ` fixes a
given ray `r` in `(T₀.1 : E →ₗ[ℝ] F).detLine`. -/
theorem orientationMonodromySign_eq_one_iff_apply {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath r = r := by
  simp [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_one_iff_apply _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.eq_symm_apply]

/-- `orientationMonodromySign` equals `-1` if and only if orientation transport along `γ` reverses a
given ray `r` in `(T₀.1 : E →ₗ[ℝ] F).detLine`. -/
theorem orientationMonodromySign_eq_neg_one_iff_apply {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = -1 ↔ quotientOrientationTransport γ.toPath r = -r := by
  simp only [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_neg_one_iff_apply _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.trans_apply,
    ← orientationEquivRay_symm_neg, Equiv.eq_symm_apply, iff_self]

/-- A loop class based at `T₀` has orientation monodromy sign `1` if and only if its orientation
transport is the identity. -/
theorem orientationMonodromySign_eq_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath = Equiv.refl _ := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine))
  refine ⟨fun h ↦ Equiv.ext fun r ↦ (orientationMonodromySign_eq_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_one_iff_apply γ r₀).2 ?_⟩
  simp [h]

/-- A loop class based at `T₀` has orientation monodromy sign `-1` if and only if its orientation
transport reverses every determinant-line orientation. -/
theorem orientationMonodromySign_eq_neg_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = -1 ↔
      ∀ r, quotientOrientationTransport γ.toPath r = -r := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine))
  exact ⟨fun h r ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r₀).2 (h r₀)⟩

end FredholmDetLine

end TauCeti
